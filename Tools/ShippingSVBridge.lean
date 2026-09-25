import Tools.ShippingPrintEntrySoundness

/-! # Interpreting the assignments in the actual emitted tree

The forward-emission theorem returns `CombStep`s, while the shipping printer
bridge returns an `SVModule`. This file connects those representations before
composing with the source theorem. The forward check and initial boundedness
remain explicit; no lexical or external-tool correctness is asserted.
-/
namespace Tools.ShippingSVBridge

open Lean Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab Sparkle.IR.OptCheck

/-- The printer includes output ports, unlike the source proof's wire-only
`declWidth`. Undeclared names have width zero. -/
def forwardWidths (m : Sparkle.IR.AST.Module) : WEnv := fun x =>
  (printWidths (m.wires ++ m.inputs ++ m.outputs) x).getD 0

/-- A forward check plus the width agreement needed to transport the OLD IR
evaluation to the printer's width environment. Checks all read names, not
only output expressions. This is not yet automatically discharged at entry. -/
def forwardCheck (m : Sparkle.IR.AST.Module) : Bool :=
  m.body.all (fun st => match st with
    | .assign _ rhs => (Sparkle.IR.Reorder.refsOf rhs).all fun x =>
        Sparkle.IR.RegDedup.declWidth m x == forwardWidths m x
    | _ => false) &&
  assignsCheck (printWidths (m.wires ++ m.inputs ++ m.outputs)) (forwardWidths m) m.body

theorem evalAssigns_widths (body : List Stmt) (we we' : WEnv) (mems : MEnv)
    (hs : ∀ st ∈ body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (hw : ∀ l r, Stmt.assign l r ∈ body → ∀ x ∈ Sparkle.IR.Reorder.refsOf r, we x = we' x)
    (env : Env) : evalAssigns we mems body env = evalAssigns we' mems body env := by
  induction body generalizing env with
  | nil => rfl
  | cons st rest ih =>
    obtain ⟨l, r, rfl, _⟩ := hs st (by simp)
    simp only [evalAssigns]
    rw [Tools.ConeFold.evalExpr_we_congr we we' env r (hw l r (by simp))]
    congr 1
    funext v
    exact ih (fun st h => hs st (by simp [h]))
      (fun l r h => hw l r (by simp [h])) _

theorem forwardCheck_sound {m : Sparkle.IR.AST.Module} (hc : forwardCheck m = true) :
    (∀ l r, Stmt.assign l r ∈ m.body → ∀ x ∈ Sparkle.IR.Reorder.refsOf r,
      Sparkle.IR.RegDedup.declWidth m x = forwardWidths m x) ∧
    assignsCheck (printWidths (m.wires ++ m.inputs ++ m.outputs)) (forwardWidths m) m.body = true := by
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨?_, hc⟩
  intro l r hs x hx
  have hr := List.all_eq_true.mp hr (.assign l r) hs
  exact beq_iff_eq.mp (List.all_eq_true.mp hr x hx)

/-- Read combinational steps from the emitted tree itself. Unsupported items
fail; in particular, registers, instances and initialized wires are not skipped. -/
def combItems : List SVModuleItem → Option (List CombStep)
  | [] => some []
  | .wireDecl _ _ none :: rest => combItems rest
  | .contAssign (.ident lhs) rhs :: rest => do
      let tail ← combItems rest
      pure (.assign lhs rhs :: tail)
  | _ => none

theorem combItems_append (xs bs : List SVModuleItem) :
    combItems (xs ++ bs) = (do
      let a ← combItems xs
      let b ← combItems bs
      pure (a ++ b)) := by
  induction xs with
  | nil => simp [combItems]
  | cons a xs ih =>
    cases a with
    | contAssign lhs rhs =>
      cases lhs <;> simp [combItems, ih, Option.bind_assoc]
    | wireDecl name width init => cases init <;> simp [combItems, ih]
    | _ => simp [combItems]

theorem combItems_wires (ps : List Port) (items : List SVModuleItem)
    (h : ps.mapM astWire = some items) : combItems items = some [] := by
  induction ps generalizing items with
  | nil => simp at h; subst items; rfl
  | cons p ps ih =>
    simp only [List.mapM_cons, astWire] at h
    cases hw : widthAstOf p.ty with
    | none => simp [hw] at h
    | some w =>
      simp only [hw] at h
      cases ht : ps.mapM astWire with
      | none => simp [ht] at h
      | some tail =>
        simp [ht, Option.bind_eq_bind] at h
        subst items
        exact ih tail ht

theorem body_combItems (body : List Stmt) (wof : String → Option Nat)
    (we : WEnv) (wires : List Port)
    (hshape : ∀ st ∈ body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (hcheck : assignsCheck wof we body = true) :
    ∃ items pairs,
      body.mapM (emitAstStmt wof wires) = some items ∧
      emitAssigns wof body = some pairs ∧ combItems items.flatten = some pairs := by
  induction body with
  | nil => exact ⟨[], [], rfl, rfl, rfl⟩
  | cons st rest ih =>
    obtain ⟨l, r, rfl, hr⟩ := hshape st (by simp)
    simp only [assignsCheck, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨hs, _⟩, _⟩, _⟩, hrest⟩ := hcheck
    have hs : Sparkle.Backend.Verilog.sanitizeName l = l := by simpa using hs
    obtain ⟨sv, hv, _⟩ := emitExpr_render_all hr wof
    obtain ⟨items, pairs, hi, hp, hc⟩ := ih
      (fun st hm => hshape st (by simp [hm])) hrest
    refine ⟨[.contAssign (.ident l) sv] :: items, .assign l sv :: pairs, ?_, ?_, ?_⟩
    · simp [List.mapM_cons, emitAstStmt, hv, hs, hi]
    · simp [emitAssigns, hv, hp]
    · simp [combItems, hc]

/-- The steps in the forward semantics are precisely the assignments of the
SV tree emitted for this module, rather than an unrelated auxiliary program. -/
theorem module_combItems (m : Sparkle.IR.AST.Module) {we : WEnv} (hp : PrintableDecls m)
    (hshape : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (hc : assignsCheck (printWidths (m.wires ++ m.inputs ++ m.outputs))
      we m.body = true) :
    ∃ sv pairs, emitAstModule m = some sv ∧
      emitAssigns (printWidths (m.wires ++ m.inputs ++ m.outputs)) m.body = some pairs ∧
      combItems sv.items = some pairs := by
  obtain ⟨hprim, hparams, htypes⟩ := hp
  let iw := m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name
  obtain ⟨ins, hi, _⟩ := ports_render m.inputs (fun p hp => htypes p (by simp [hp]))
    .input (Or.inl rfl)
  obtain ⟨outs, ho, _⟩ := ports_render m.outputs (fun p hp => htypes p (by simp [hp]))
    .output (Or.inr rfl)
  obtain ⟨ws, hw, _, _⟩ := wires_render iw (fun p hp =>
    htypes p (by have := (List.mem_filter.mp hp).1; simp [this]))
  obtain ⟨bs, pairs, hb, he, hcomb⟩ := body_combItems m.body
    (printWidths (m.wires ++ m.inputs ++ m.outputs)) _ m.wires hshape hc
  refine ⟨{name := Sparkle.Backend.Verilog.sanitizeName m.name, params := [], ports := ins ++ outs, items := ws ++ bs.flatten}, pairs, ?_, he, ?_⟩
  · simp only [emitAstModule, hprim, hparams,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp (disch := (intros; rfl)) only [filterMap_assigns m.body hshape]
    simp only [List.find?_nil]
    change ((m.inputs.mapM (astPort .input)).bind fun ins =>
      (m.outputs.mapM (astPort .output)).bind fun outs =>
      (iw.mapM astWire).bind fun wires =>
      (m.body.mapM (emitAstStmt (printWidths (m.wires ++ m.inputs ++ m.outputs)) m.wires)).bind fun body =>
      some ({name := Sparkle.Backend.Verilog.sanitizeName m.name, params := [], ports := ins ++ outs, items := wires ++ body.flatten} : SVModule)) = _
    simp only [hi, ho, hw, hb, Option.bind_some]
  · simpa [combItems_append, combItems_wires iw ws hw] using hcomb

/-- Conditional forward semantics of the ACTUAL emitted module's items.
The declaration assumptions are supplied by the synthesis-entry proof; the
forward check and initial boundedness are the remaining semantic obligations. -/
theorem module_forward {m : Sparkle.IR.AST.Module} {sv : SVModule} {we : WEnv}
    (hp : PrintableDecls m)
    (hshape : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (htree : emitAstModule m = some sv)
    (hc : assignsCheck (printWidths (m.wires ++ m.inputs ++ m.outputs))
      we m.body = true)
    (mems : MEnv) (initial : Env)
    (hb : Bounded we initial)
    (hpw : ∀ x width, printWidths (m.wires ++ m.inputs ++ m.outputs) x = some width →
      initial x < 2 ^ width) :
    ∃ pairs env, combItems sv.items = some pairs ∧
      evalAssigns we mems m.body initial = some env ∧
      evalAssignsSV (printWidths (m.wires ++ m.inputs ++ m.outputs)) mems pairs initial = some env := by
  obtain ⟨sv', pairs', hemit, hsteps, hcitems⟩ := module_combItems m hp hshape hc
  rw [htree] at hemit
  cases hemit
  obtain ⟨pairs, env, hsteps', hir, hsv, _, _⟩ := emit_sem_assigns mems m.body initial hc hb hpw
  rw [hsteps] at hsteps'
  cases hsteps'
  exact ⟨pairs', env, hcitems, hir, hsv⟩

/-- Source-to-SV assignment-fold agreement for the actual emitted tree and
bytes, CONDITIONAL on the forward check and initial width bounds. These are
not yet derived by the source entry, and this is not full SV tool semantics. -/
theorem compiledFragment_forward {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hc : forwardCheck (checkedOptimize m) = true) :
    let o := checkedOptimize m
    let wof := printWidths (o.wires ++ o.inputs ++ o.outputs)
    ∃ (sv : SVModule) (port : Nat → Option String) (pairs : List CombStep),
      emitAstModule o = some sv ∧
      renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (verilogOf m) ∧
      combItems sv.items = some pairs ∧
      (∀ j j' w, port j = some w → port j' = some w → j = j') ∧
      (∀ j, j < names.length → ∃ w, port j = some w ∧ w ∈ o.inputs.map (·.name)) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv)
        (initial : Env),
        (∀ j w, j < names.length → port j = some w → initial w = ((sigs j).val t).toNat) →
        Bounded (forwardWidths o) initial →
        ∃ env, evalAssignsSV wof mems pairs initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨sv, port, htree, htext, hdist, hex, hsem⟩ := compiledFragment_artifact h henv hwf hn
  obtain ⟨hp, hg⟩ := synthesized_printFacts h henv hwf hn
  have hpo := checkedOptimize_printDecls hg hp
  have hshape := checkedOptimize_printShape hg
  obtain ⟨hwidths, hc⟩ := forwardCheck_sound hc
  obtain ⟨sv', pairs, htree', _, hitems⟩ := module_combItems _ hpo hshape hc
  rw [htree] at htree'
  cases htree'
  refine ⟨sv, port, pairs, htree, htext, hitems, hdist, hex, ?_⟩
  intro dom sigs t mems initial hinput hb
  have hpw : ∀ x width, printWidths ((checkedOptimize m).wires ++
      (checkedOptimize m).inputs ++ (checkedOptimize m).outputs) x = some width →
      initial x < 2 ^ width := by
    intro x width hx
    have h := hb x
    simpa only [forwardWidths, hx, Option.getD_some] using h
  obtain ⟨env, hir, hout⟩ := hsem sigs t mems initial hinput
  rw [evalAssigns_widths _ _ _ mems hshape hwidths initial] at hir
  obtain ⟨pairs', env', hitems', hir', hsv⟩ := module_forward hpo hshape htree hc mems initial hb hpw
  rw [hitems] at hitems'
  cases hitems'
  rw [hir] at hir'
  cases hir'
  exact ⟨env, hsv, hout⟩

end Tools.ShippingSVBridge
