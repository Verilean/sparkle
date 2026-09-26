import Tools.ShippingPrintSoundness

/-! # Module text from the existing SV AST

The renderer consumes only an SVModule, a comment label and a layout count.
The latter separates declaration lines from assignments for blank-line layout;
both portions are checked against their AST constructors. It is not another
IR emitter. Identifier legality and the interpretation of text as SV grammar
remain separate from the byte-equality theorem.
-/
namespace Tools.ShippingModulePrintSoundness

open Sparkle.IR.AST Sparkle.IR.Type
open Tools.SVParser.AST Tools.SVParser.EmitAst
open Tools.ShippingPrintSoundness Tools.ShippingOptSoundness
open Sparkle.Backend.Verilog (sanitizeName)

def renderType : Option (Nat × Nat) → String
  | none => "logic"
  | some (hi, lo) => s!"logic [{hi}:{lo}]"

def renderPort (p : SVPort) : Option String := do
  if p.isReg || p.isSigned || p.widthExpr.isSome then none else
  let dir ← match p.dir with
    | .input => some "input"
    | .output => some "output"
    | _ => none
  some s!"{dir} {renderType p.width} {p.name}"

def renderWire : SVModuleItem → Option String
  | .wireDecl name w none => some s!"    {renderType w} {name};"
  | _ => none

/-- `commentName` supplies the single-line source label (LF/CR normalized)
separately from the sanitized AST name. `wireCount` controls whitespace only;
wrong item kinds fail. -/
def renderModule (commentName : String) (wireCount : Nat) (sv : SVModule) : Option String := do
  if !sv.params.isEmpty then none else
  let ps ← sv.ports.mapM renderPort
  let ws ← (sv.items.take wireCount).mapM renderWire
  let bs ← (sv.items.drop wireCount).mapM (renderItem "    ")
  let ports := if ps.isEmpty then "" else "\n    " ++ String.intercalate ",\n    " ps ++ "\n"
  let wires := if ws.isEmpty then "" else "\n" ++ String.intercalate "\n" ws ++ "\n" ++ "\n"
  let body := if bs.isEmpty then "" else "\n" ++ String.intercalate "\n\n" bs ++ "\n"
  some (Sparkle.Backend.Verilog.moduleComment commentName ++
    s!"module {sv.name} " ++ s!"({ports});\n" ++ wires ++ body ++ "\nendmodule\n")

/-- A source label cannot end its generated line comment early. -/
def LineText (s : String) : Prop := ∀ c ∈ s.toList, c ≠ '\n' ∧ c ≠ '\r'

theorem commentLabel_lineText (s : String) :
    LineText (Sparkle.Backend.Verilog.commentLabel s) := by
  unfold Sparkle.Backend.Verilog.commentLabel
  split
  · rename_i h
    simpa [LineText, String.all_bool_eq] using h
  · intro c hc
    simp only [String.toList_map, List.mem_map] at hc
    obtain ⟨a, _, rfl⟩ := hc
    split <;> simp_all

theorem commentLabel_eq {s : String} (h : LineText s) :
    Sparkle.Backend.Verilog.commentLabel s = s := by
  unfold Sparkle.Backend.Verilog.commentLabel
  have hs : s.all (fun c => c != '\n' && c != '\r') = true := by
    simpa [LineText, String.all_bool_eq] using h
  rw [hs, if_pos rfl]

/-- This concerns the actual rendered prefix, not a hypothetical label.
The rest of the module still needs an identifier and grammar contract. -/
theorem renderModule_comment {name : String} {count : Nat} {sv : SVModule} {text : String}
    (h : renderModule name count sv = some text) :
    LineText (Sparkle.Backend.Verilog.commentLabel name) ∧
      ∃ rest, text = Sparkle.Backend.Verilog.moduleComment name ++ rest := by
  unfold renderModule at h
  split at h
  · cases h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨ps, _, ws, _, bs, _, he⟩ := h
    cases he
    let ports := if ps.isEmpty then "" else "\n    " ++ String.intercalate ",\n    " ps ++ "\n"
    let wires := if ws.isEmpty then "" else "\n" ++ String.intercalate "\n" ws ++ "\n" ++ "\n"
    let body := if bs.isEmpty then "" else "\n" ++ String.intercalate "\n\n" bs ++ "\n"
    refine ⟨commentLabel_lineText name,
      s!"module {sv.name} " ++ s!"({ports});\n" ++ wires ++ body ++ "\nendmodule\n", ?_⟩
    simp only [ports, wires, body, String.append_assoc]

inductive PrintableType : HWType → Prop
  | bit : PrintableType .bit
  | bits (n : Nat) : 0 < n → PrintableType (.bitVector n)

theorem type_render {ty : HWType} (h : PrintableType ty) :
    ∃ w, widthAstOf ty = some w ∧ renderType w = Sparkle.Backend.Verilog.emitType ty := by
  cases h with
  | bit => exact ⟨none, rfl, rfl⟩
  | bits n hn =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => exact ⟨none, rfl, rfl⟩
      | succ n => exact ⟨some (n + 1, 0), rfl, by
          simp [renderType, Sparkle.Backend.Verilog.emitType]
          simp only [String.append_assoc]
          rfl⟩

def astPort (dir : SVPortDir) (p : Port) : Option SVPort := do
  let w ← widthAstOf p.ty
  some { dir, isReg := false, width := w, name := sanitizeName p.name, widthExpr := none, isSigned := false }

def astWire (p : Port) : Option SVModuleItem := do
  let w ← widthAstOf p.ty
  some (.wireDecl (sanitizeName p.name) w none)

/-- Interpret a literal packed range from the emitted port itself, without
consulting the IR width table. Symbolic ranges remain outside this bridge. -/
def declaredPortWidth (p : SVPort) : Option Nat :=
  if p.widthExpr.isSome then none else
    some (match p.width with
      | none => 1
      | some (hi, lo) => max hi lo - min hi lo + 1)

theorem astPort_bits {p : Port} {n : Nat} (ht : p.ty = .bitVector n) (hn : 0 < n)
    (dir : SVPortDir) {sp : SVPort} (h : astPort dir p = some sp) :
    sp.dir = dir ∧ sp.name = sanitizeName p.name ∧
      declaredPortWidth sp = some n ∧ sp.isSigned = false := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      simp [astPort, ht, widthAstOf] at h
      subst sp
      exact ⟨rfl, rfl, rfl, rfl⟩
    | succ n =>
      simp [astPort, ht, widthAstOf] at h
      subst sp
      simp [declaredPortWidth]

private theorem mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => cases hx
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, bs, hbs, he⟩ := h
    cases he
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨y, hy, he⟩ := ih hbs hx
      exact ⟨y, List.mem_cons_of_mem _ hy, he⟩

theorem emitAstModule_ports {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (h : emitAstModule m = some sv) :
    ∃ ins outs, m.inputs.mapM (astPort .input) = some ins ∧
      m.outputs.mapM (astPort .output) = some outs ∧ sv.ports = ins ++ outs := by
  unfold emitAstModule at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨ins, hi, outs, ho, ws, hw, bs, hb, he⟩ := h
      cases he
      exact ⟨ins, outs, hi, ho, rfl⟩

/-- Every positive-width IR input becomes an unsigned port of that width
in the actual emitted tree. This includes unused inputs. -/
theorem emitAstModule_input {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (h : emitAstModule m = some sv) {p : Port} (hp : p ∈ m.inputs)
    {n : Nat} (ht : p.ty = .bitVector n) (hn : 0 < n) :
    ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = sanitizeName p.name ∧
      declaredPortWidth sp = some n ∧ sp.isSigned = false := by
  obtain ⟨ins, outs, hi, _, he⟩ := emitAstModule_ports h
  obtain ⟨sp, hsp, hs⟩ := mapM_mem hi hp
  exact ⟨sp, he ▸ List.mem_append_left outs hsp, astPort_bits ht hn .input hs⟩

/-- Read a combinational unsigned output's width from the emitted AST alone.
Input ports of the same spelling do not count as output declarations. -/
def declaredOutputWidth (sv : SVModule) (name : String) : Option Nat :=
  (sv.ports.find? fun p => p.dir == .output && p.name == name).bind fun p =>
    if p.isSigned || p.isReg then none else declaredPortWidth p

/-- Observe the low declared-width bits of an assignment environment at an
unsigned output. This is an observation of the subset evaluator, not a model
of concurrent scheduling or four-state SystemVerilog. -/
def observeUnsignedOutput (sv : SVModule) (env : String → Nat) (name : String) : Option Nat := do
  let n ← declaredOutputWidth sv name
  some (env name % 2 ^ n)

private theorem astPort_dir {dir : SVPortDir} {p : Port} {sp : SVPort}
    (h : astPort dir p = some sp) : sp.dir = dir := by
  simp only [astPort, bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, _, he⟩ := h
  cases he
  rfl

theorem ports_dir {ps : List Port} {sps : List SVPort} {dir : SVPortDir}
    (h : ps.mapM (astPort dir) = some sps) : ∀ p ∈ sps, p.dir = dir := by
  induction ps generalizing sps with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst sps; simp
  | cons p ps ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨sp, hp, sps', hps, he⟩ := h
    cases he
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact astPort_dir hp
    · exact ih hps q hq

/-- The declared range of the actual emitted single output has the source
width. This includes the scalar spelling at width one. -/
theorem emitAstModule_outputWidth {m : Sparkle.IR.AST.Module} {sv : SVModule}
    {p : Port} {n : Nat} (h : emitAstModule m = some sv) (ho : m.outputs = [p])
    (ht : p.ty = .bitVector n) (hn : 0 < n) :
    declaredOutputWidth sv (sanitizeName p.name) = some n := by
  obtain ⟨ins, outs, hi, hs, he⟩ := emitAstModule_ports h
  obtain ⟨w, hw, _⟩ := type_render (PrintableType.bits n hn)
  rw [ho] at hs
  simp [List.mapM_cons, astPort, ht, hw] at hs
  subst outs
  have hb := astPort_bits ht hn .output (p := p)
    (show astPort .output p = some { dir := .output, name := sanitizeName p.name, width := w } by
      simp [astPort, ht, hw])
  unfold declaredOutputWidth
  rw [he, List.find?_append]
  have hnone : ins.find? (fun sp => sp.dir == .output && sp.name == sanitizeName p.name) = none := by
    apply List.find?_eq_none.mpr
    intro sp hp
    simp [ports_dir hi sp hp, show (SVPortDir.input == .output) = false from rfl]
  simp [hnone, show (SVPortDir.output == .output) = true from rfl, hb.2.2.1]

theorem observeUnsignedOutput_eq {sv : SVModule} {env : String → Nat} {name : String}
    {n : Nat} {value : BitVec n} (hw : declaredOutputWidth sv name = some n)
    (hv : env name = value.toNat) :
    observeUnsignedOutput sv env name = some value.toNat := by
  simp [observeUnsignedOutput, hw, hv, Nat.mod_eq_of_lt value.isLt]

theorem port_render (p : Port) (h : PrintableType p.ty)
    (dir : SVPortDir) (hd : dir = .input ∨ dir = .output) :
    ∃ sp, astPort dir p = some sp ∧ renderPort sp = some
      s!"{if dir == .input then "input" else "output"} {Sparkle.Backend.Verilog.emitType p.ty} {sanitizeName p.name}" := by
  obtain ⟨w, hw, ht⟩ := type_render h
  rcases hd with rfl | rfl <;>
    (simp [astPort, hw, renderPort, ht]; rfl)

theorem ports_render (ps : List Port) (h : ∀ p ∈ ps, PrintableType p.ty)
    (dir : SVPortDir) (hd : dir = .input ∨ dir = .output) :
    ∃ sps, ps.mapM (astPort dir) = some sps ∧
      sps.mapM renderPort = some (ps.map fun p =>
        s!"{if dir == .input then "input" else "output"} {Sparkle.Backend.Verilog.emitType p.ty} {sanitizeName p.name}") := by
  induction ps with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨sp, hp, hr⟩ := port_render p (h p (by simp)) dir hd
    obtain ⟨sps, hps, hrs⟩ := ih (fun p hp => h p (by simp [hp]))
    exact ⟨sp :: sps, by simp [List.mapM_cons, hp, hps],
      by simp [List.mapM_cons, hr, hrs]⟩

theorem wires_render (ps : List Port) (h : ∀ p ∈ ps, PrintableType p.ty) :
    ∃ items, ps.mapM astWire = some items ∧ items.length = ps.length ∧
      items.mapM renderWire = some (ps.map fun p =>
        s!"    {Sparkle.Backend.Verilog.emitType p.ty} {sanitizeName p.name};") := by
  induction ps with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨w, hw, ht⟩ := type_render (h p (by simp))
    obtain ⟨items, hi, hl, hr⟩ := ih (fun p hp => h p (by simp [hp]))
    refine ⟨.wireDecl (sanitizeName p.name) w none :: items, ?_, by simp [hl], ?_⟩
    · simp [List.mapM_cons, astWire, hw, hi]
    · simp [List.mapM_cons, renderWire, ht, hr]

theorem body_lines (body : List Stmt) (widths resetWires : List Port)
    (h : ∀ st ∈ body, ∃ lhs rhs, st = .assign lhs rhs ∧ PrintShape rhs) :
    ∃ items, body.mapM (emitAstStmt (printWidths widths) resetWires) = some items ∧
      items.flatten.mapM (renderItem "    ") = some (body.map fun st =>
        Sparkle.Backend.Verilog.emitStmt st "    " widths) := by
  induction body with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons st body ih =>
    obtain ⟨lhs, rhs, rfl, hs⟩ := h st (by simp)
    obtain ⟨item, hi, hr⟩ := emitStmt_render_all hs lhs "    " widths
    have hi' : emitAstStmt (printWidths widths) resetWires (.assign lhs rhs) = some [item] := by
      simpa only [emitAstStmt] using hi
    obtain ⟨items, his, hrs⟩ := ih (fun s hs => h s (by simp [hs]))
    exact ⟨[item] :: items, by simp [List.mapM_cons, hi', his],
      by simp [List.mapM_cons, hr, hrs]⟩

theorem filterMap_assigns {α : Type} (body : List Stmt)
    (h : ∀ st ∈ body, ∃ lhs rhs, st = .assign lhs rhs ∧ PrintShape rhs)
    (f : Stmt → Option α) (hf : ∀ l r, f (.assign l r) = none) :
    body.filterMap f = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro st hs
  obtain ⟨l, r, rfl, _⟩ := h st hs
  exact hf l r

/-- Byte equality for the ENTIRE shipping module, including the original
comment name, port filtering, declarations and all blank lines. No parser is
executed or assumed. Positive concrete port/wire types and the expression
grammar are explicit hypotheses, not yet derived from the synthesis entry. -/
theorem emitModule_render (m : Sparkle.IR.AST.Module)
    (hprim : m.isPrimitive = false) (hparams : m.parameters = [])
    (htypes : ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, PrintableType p.ty)
    (hbody : ∀ st ∈ m.body, ∃ lhs rhs, st = .assign lhs rhs ∧ PrintShape rhs) :
    ∃ sv, emitAstModule m = some sv ∧
      renderModule m.name
        (m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name).length sv
        = some (Sparkle.Backend.Verilog.toVerilog m) := by
  let iw := m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name
  obtain ⟨ins, hi, hir⟩ := ports_render m.inputs (fun p hp => htypes p (by simp [hp]))
    .input (Or.inl rfl)
  obtain ⟨outs, ho, hor⟩ := ports_render m.outputs (fun p hp => htypes p (by simp [hp]))
    .output (Or.inr rfl)
  obtain ⟨ws, hw, hwl, hwr⟩ := wires_render iw (fun p hp =>
    htypes p (by have := (List.mem_filter.mp hp).1; simp [this]))
  obtain ⟨bs, hb, hbr⟩ := body_lines m.body (m.wires ++ m.inputs ++ m.outputs) m.wires hbody
  refine ⟨{ name := sanitizeName m.name, params := [], ports := ins ++ outs, items := ws ++ bs.flatten }, ?_, ?_⟩
  · simp only [emitAstModule, hprim, hparams,
      List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp (disch := (intros; rfl)) only [filterMap_assigns m.body hbody]
    simp only [List.find?_nil]
    change ((m.inputs.mapM (astPort .input)).bind fun ins =>
      (m.outputs.mapM (astPort .output)).bind fun outs =>
      (iw.mapM astWire).bind fun wires =>
      (m.body.mapM (emitAstStmt (printWidths (m.wires ++ m.inputs ++ m.outputs)) m.wires)).bind fun body =>
      some ({ name := sanitizeName m.name, params := [], ports := ins ++ outs, items := wires ++ body.flatten } : SVModule)) = _
    simp only [hi, ho, hw, hb, Option.bind_some]
  · simp only [Sparkle.Backend.Verilog.toVerilog, Sparkle.Backend.Verilog.emitModule,
      hprim, hparams, Bool.false_eq_true, ↓reduceIte,
      Sparkle.Backend.Verilog.emitParameterList, List.isEmpty_nil]
    simp (disch := (intros; rfl)) only [filterMap_assigns m.body hbody]
    simp only [renderModule]
    rw [← hwl]
    simp only [List.take_left, List.drop_left, List.mapM_append, hir, hor, hwr, hbr]
    have hI : (SVPortDir.input == SVPortDir.input) = true := rfl
    have hO : (SVPortDir.output == SVPortDir.input) = false := rfl
    simp [Sparkle.Backend.Verilog.emitPortList, Sparkle.Backend.Verilog.emitWireDecls,
      iw, String.append_assoc, hI, hO, ToString.toString]
    split <;> simp_all [String.append_assoc]

/-- The optimizer check discharges the body-shape hypothesis. Declaration
premises are explicit here; the entry bridge derives them on both branches. -/
theorem acceptedOptimizer_module_render {m o : Sparkle.IR.AST.Module}
    (h : Sparkle.IR.OptCheck.optCheck m o = true)
    (hprim : o.isPrimitive = false) (hparams : o.parameters = [])
    (htypes : ∀ p ∈ o.inputs ++ o.outputs ++ o.wires, PrintableType p.ty) :
    ∃ sv, emitAstModule o = some sv ∧
      renderModule o.name
        (o.wires.filter fun p => !((o.inputs ++ o.outputs).map (·.name)).contains p.name).length sv
        = some (Sparkle.Backend.Verilog.toVerilog o) := by
  apply emitModule_render o hprim hparams htypes
  have h := (Bool.and_eq_true_iff.mp h).1
  unfold Sparkle.IR.OptCheck.optCheckCore at h
  dsimp only at h
  split at h
  · rename_i dm ds hm ho
    intro st hs
    obtain ⟨l, r, he, hr⟩ := normBody_input_shape _ _ _ _ _ ho st hs
    exact ⟨l, r, he, PrintShape.ofShape hr⟩
  · cases h

end Tools.ShippingModulePrintSoundness
