import Tools.ShippingSVBridge

/-! # Widths from the actual emitted declarations

The subset evaluator previously received the IR/printer's width lookup.
Here the lookup is constructed from SV ports and wire declarations instead.
The proofs account for port-name wire suppression and lookup order. This
does not establish lexical validity or concurrent/four-state semantics.
-/
namespace Tools.ShippingDeclWidths

open Lean Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingModulePrintSoundness Tools.ShippingPrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingEntrySoundness
open Tools.ShippingSVBridge Tools.ShippingOptSoundness
open Tools.ShippingTranslateSoundness Tools.ShippingScalarSoundness
open Tools.ShippingPostSoundness
open Sparkle.Backend.Verilog (sanitizeName)

def typeWidth : HWType → Option Nat
  | .bitVector n => some n
  | .bit => some 1
  | _ => none

def irTable (ps : List Port) : List (String × Option Nat) :=
  ps.map fun p => (Sparkle.Backend.Verilog.sanitizeName p.name, typeWidth p.ty)

def wireEntry : SVModuleItem → Option (String × Option Nat)
  | .wireDecl name width _ =>
      some (name, some (match width with
        | none => 1
        | some (hi, lo) => max hi lo - min hi lo + 1))
  | _ => none

/-- Ports precede internal declarations, as they do in the emitted module.
This uses the AST only; it does not read an IR module or supplied width table. -/
def declarationTable (sv : SVModule) : List (String × Option Nat) :=
  sv.ports.map (fun p => (p.name, declaredPortWidth p)) ++ sv.items.filterMap wireEntry

def lookupTable (table : List (String × Option Nat)) (x : String) : Option Nat :=
  (table.find? fun p => p.1 == x).bind (·.2)

def astWidths (sv : SVModule) : String → Option Nat := lookupTable (declarationTable sv)

theorem lookup_irTable (ps : List Port) (x : String) :
    lookupTable (irTable ps) x = printWidths ps x := by
  simp only [lookupTable, irTable, List.find?_map, Option.bind_map]
  rfl

theorem astPort_entry {p : Port} {sp : SVPort} {dir : SVPortDir}
    (ht : PrintableType p.ty) (h : astPort dir p = some sp) :
    (sp.name, declaredPortWidth sp) = (Sparkle.Backend.Verilog.sanitizeName p.name, typeWidth p.ty) := by
  rcases p with ⟨name, ty⟩
  cases ht with
  | bit =>
    simp [astPort, widthAstOf] at h
    subst sp
    rfl
  | bits n hn =>
    obtain ⟨_, hn', hw, _⟩ := astPort_bits rfl hn dir h
    exact Prod.ext hn' hw

theorem ports_table {ps : List Port} {sps : List SVPort} {dir : SVPortDir}
    (ht : ∀ p ∈ ps, PrintableType p.ty) (h : ps.mapM (astPort dir) = some sps) :
    sps.map (fun p => (p.name, declaredPortWidth p)) = irTable ps := by
  induction ps generalizing sps with
  | nil => simp at h; subst sps; rfl
  | cons p ps ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨sp, hp, rest, hr, he⟩ := h
    cases he
    simp only [List.map_cons, irTable]
    rw [astPort_entry (ht p (by simp)) hp, ih (fun p hp => ht p (by simp [hp])) hr]
    rfl

theorem astWire_entry {p : Port} {item : SVModuleItem}
    (ht : PrintableType p.ty) (h : astWire p = some item) :
    wireEntry item = some (Sparkle.Backend.Verilog.sanitizeName p.name, typeWidth p.ty) := by
  rcases p with ⟨name, ty⟩
  cases ht with
  | bit => simp [astWire, widthAstOf] at h; subst item; rfl
  | bits n hn =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => simp [astWire, widthAstOf] at h; subst item; rfl
      | succ n =>
        simp [astWire, widthAstOf] at h
        subst item
        simp [wireEntry, typeWidth]

theorem wires_table {ps : List Port} {items : List SVModuleItem}
    (ht : ∀ p ∈ ps, PrintableType p.ty) (h : ps.mapM astWire = some items) :
    items.filterMap wireEntry = irTable ps := by
  induction ps generalizing items with
  | nil => simp at h; subst items; rfl
  | cons p ps ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨item, hp, rest, hr, he⟩ := h
    cases he
    simp only [List.filterMap_cons, astWire_entry (ht p (by simp)) hp]
    rw [ih (fun p hp => ht p (by simp [hp])) hr]
    rfl

theorem body_no_declarations {body : List Stmt} {items : List (List SVModuleItem)}
    (wof : String → Option Nat) (wires : List Port)
    (hs : ∀ st ∈ body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (h : body.mapM (emitAstStmt wof wires) = some items) :
    items.flatten.filterMap wireEntry = [] := by
  induction body generalizing items with
  | nil => simp at h; subst items; rfl
  | cons st body ih =>
    obtain ⟨l, r, rfl, _⟩ := hs st (by simp)
    simp only [List.mapM_cons, emitAstStmt, bind, Option.bind_eq_some_iff] at h
    obtain ⟨head, ⟨expr, _, he⟩, rest, hr, ht⟩ := h
    cases he
    cases ht
    simpa [wireEntry] using ih (fun st hm => hs st (by simp [hm])) hr

def visibleDecls (m : Sparkle.IR.AST.Module) : List Port :=
  m.inputs ++ m.outputs ++
    m.wires.filter (fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name)

theorem declarationTable_emitted {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (hp : PrintableDecls m)
    (hs : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (h : emitAstModule m = some sv) :
    declarationTable sv = irTable (visibleDecls m) := by
  obtain ⟨hprim, hparams, htypes⟩ := hp
  simp only [emitAstModule, hprim, hparams, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  simp (disch := (intros; rfl)) only [filterMap_assigns m.body hs] at h
  simp only [List.find?_nil] at h
  change ((m.inputs.mapM (astPort .input)).bind fun ins =>
    (m.outputs.mapM (astPort .output)).bind fun outs =>
    ((m.wires.filter fun p => !((m.inputs ++ m.outputs).map (·.name)).contains p.name).mapM astWire).bind fun ws =>
    (m.body.mapM (emitAstStmt (printWidths (m.wires ++ m.inputs ++ m.outputs)) m.wires)).bind fun bs =>
    some ({name := Sparkle.Backend.Verilog.sanitizeName m.name, params := [], ports := ins ++ outs, items := ws ++ bs.flatten} : SVModule)) = some sv at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨ins, hi, outs, ho, ws, hw, bs, hb, he⟩ := h
  cases he
  have hin := ports_table (fun p hp => htypes p (by simp [hp])) hi
  have hout := ports_table (fun p hp => htypes p (by simp [hp])) ho
  have hwire := wires_table (fun p hp => htypes p (by
    have := (List.mem_filter.mp hp).1; simp [this])) hw
  have hbody := body_no_declarations _ _ hs hb
  simp only [declarationTable, List.map_append, List.filterMap_append, hin, hout, hwire, hbody,
    List.append_nil, visibleDecls, irTable, List.map_append]

/-- Reordering or suppressing redundant declarations does not affect lookup
when a printed name has a unique declared type. -/
theorem printWidths_ext {as bs : List Port}
    (hm : ∀ p, p ∈ as ↔ p ∈ bs)
    (hc : ∀ p ∈ as, ∀ q ∈ as,
      Sparkle.Backend.Verilog.sanitizeName p.name = Sparkle.Backend.Verilog.sanitizeName q.name → p.ty = q.ty) :
    printWidths as = printWidths bs := by
  funext x
  unfold printWidths
  cases ha : as.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) with
  | none =>
    have hb : bs.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) = none := by
      rw [List.find?_eq_none] at ha ⊢
      exact fun p hp => ha p ((hm p).mpr hp)
    simp [hb]
  | some p =>
    have hp := List.mem_of_find?_eq_some ha
    have hpx : Sparkle.Backend.Verilog.sanitizeName p.name = x := by simpa using List.find?_some ha
    cases hb : bs.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) with
    | none =>
      have hf := List.find?_eq_none.mp hb p ((hm p).mp hp)
      simp [hpx] at hf
    | some q =>
      have hq := (hm q).mpr (List.mem_of_find?_eq_some hb)
      have hqx : Sparkle.Backend.Verilog.sanitizeName q.name = x := by simpa using List.find?_some hb
      simp only [Option.bind_some, hc p hp q hq (hpx.trans hqx.symm)]

/-- A wire hidden by a port is the very same declaration, not merely a
name match with a possibly different width. -/
theorem visibleDecls_mem {m : Sparkle.IR.AST.Module}
    (hc : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs,
      ∀ q ∈ m.wires ++ m.inputs ++ m.outputs, p.name = q.name → p = q) :
    ∀ p, p ∈ visibleDecls m ↔ p ∈ m.wires ++ m.inputs ++ m.outputs := by
  intro p
  simp only [visibleDecls, List.mem_append, List.mem_filter]
  constructor
  · rintro ((hi | ho) | ⟨hw, _⟩)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr ho
    · exact Or.inl (Or.inl hw)
  · rintro ((hw | hi) | ho)
    · by_cases hport : p.name ∈ (m.inputs ++ m.outputs).map (·.name)
      · obtain ⟨q, hq, he⟩ := List.mem_map.mp hport
        have eq := hc p (by simp [hw]) q (by simpa [List.mem_append, or_assoc] using Or.inr hq) he.symm
        subst q
        exact Or.inl (by simpa using hq)
      · exact Or.inr ⟨hw, by simpa using hport⟩
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr ho)

theorem astWidths_emitted {m : Sparkle.IR.AST.Module} {sv : SVModule}
    (hp : PrintableDecls m)
    (hs : ∀ st ∈ m.body, ∃ l r, st = .assign l r ∧ PrintShape r)
    (hn : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hc : ∀ p ∈ m.wires ++ m.inputs ++ m.outputs,
      ∀ q ∈ m.wires ++ m.inputs ++ m.outputs, p.name = q.name → p = q)
    (h : emitAstModule m = some sv) :
    astWidths sv = printWidths (m.wires ++ m.inputs ++ m.outputs) := by
  funext x
  unfold astWidths
  rw [declarationTable_emitted hp hs h, lookup_irTable]
  have he := printWidths_ext (fun p => (visibleDecls_mem hc p).symm) (by
    intro p hp q hq he
    rw [hn p hp, hn q hq] at he
    exact congrArg Port.ty (hc p hp q hq he))
  exact congrFun he.symm x

/-- Actual optimized declarations inherit both clean names and uniqueness
of the declaration attached to each name from the synthesis entry. -/
theorem compiled_declarations {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    let o := checkedOptimize m
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) ∧
    (∀ p ∈ o.wires ++ o.inputs ++ o.outputs,
      ∀ q ∈ o.wires ++ o.inputs ++ o.outputs, p.name = q.name → p = q) := by
  have hg := (synthesized_printFacts h henv hwf hn).2
  obtain ⟨hiO, hoO⟩ := checkedOptimize_ports hg
  obtain ⟨m0, _, _, hcore, hm⟩ := synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, hev, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, ho⟩ := postprocess_sound hn hpr hm hev
  have hsub : ∀ p ∈ (checkedOptimize m).wires ++ (checkedOptimize m).inputs ++
      (checkedOptimize m).outputs, p ∈ m0.wires ∨ p = {name := "out", ty := .bitVector n} := by
    intro p hp
    simp only [List.mem_append, hiO, hoO, hi, ho, hpr.2.2.2.1 hn, List.mem_singleton] at hp
    rcases hp with (hp | hp) | hp
    · exact Or.inl (postprocess_wires_subset hn hpr hm p (checkedOptimize_wires_subset m p hp))
    · obtain ⟨_, _, _, hty, hw⟩ := hins p hp
      have he : p = {name := p.name, ty := .bitVector n} := by cases p; simp_all
      exact Or.inl (he ▸ hw)
    · exact Or.inr hp
  constructor
  · intro p hp
    rcases hsub p hp with hp | rfl
    · exact sanitizeName_of_clean (hpr.2.2.2.2.1.2.2.2 p hp).1
    · simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  · intro p hp q hq he
    rcases hsub p hp with hp | rfl <;> rcases hsub q hq with hq | rfl
    · have hf := find?_of_nodup hpr.1 hp
      have hf' := find?_of_nodup hpr.1 hq
      rw [he, hf'] at hf
      exact (Option.some.inj hf).symm
    · apply False.elim; apply hpr.2.1
      have hm := List.mem_map_of_mem (f := Port.name) hp
      simpa only [he] using hm
    · apply False.elim; apply hpr.2.1
      have hm := List.mem_map_of_mem (f := Port.name) hq
      simpa only [← he] using hm
    · rfl

/-- Every emitted data declaration is an allocated underscore-leading name
or the fixed output name, inherited from the actual synthesis run. -/
theorem compiled_dataNames {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∀ p ∈ (checkedOptimize m).wires ++ (checkedOptimize m).inputs ++
        (checkedOptimize m).outputs, Sparkle.IR.NameHints.DataName p.name := by
  have hg := (synthesized_printFacts h henv hwf hn).2
  obtain ⟨hiO, hoO⟩ := checkedOptimize_ports hg
  obtain ⟨m0, _, _, hcore, hm⟩ := synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, hev, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, ho⟩ := postprocess_sound hn hpr hm hev
  have hsub : ∀ p ∈ (checkedOptimize m).wires ++ (checkedOptimize m).inputs ++
      (checkedOptimize m).outputs, p ∈ m0.wires ∨ p = {name := "out", ty := .bitVector n} := by
    intro p hp
    simp only [List.mem_append, hiO, hoO, hi, ho, hpr.2.2.2.1 hn, List.mem_singleton] at hp
    rcases hp with (hp | hp) | hp
    · exact Or.inl (postprocess_wires_subset hn hpr hm p (checkedOptimize_wires_subset m p hp))
    · obtain ⟨_, _, _, hty, hw⟩ := hins p hp
      have he : p = {name := p.name, ty := .bitVector n} := by cases p; simp_all
      exact Or.inl (he ▸ hw)
    · exact Or.inr hp
  intro p hp
  rcases hsub p hp with hp | rfl
  · exact Or.inl (hpr.2.2.2.2.1.2.2.2 p hp)
  · exact Or.inr rfl

/-- Name class of the actual AST's declared ports and wires. Module names,
references and textual tokenization are not asserted by this declaration fact. -/
theorem compiled_astDataNames {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr} {sv : SVModule}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (ht : emitAstModule (checkedOptimize m) = some sv) :
    ∀ entry ∈ declarationTable sv, Sparkle.IR.NameHints.DataName entry.1 := by
  obtain ⟨hnames, hc⟩ := compiled_declarations h henv hwf hn
  rw [declarationTable_emitted (printed_printDecls h henv hwf hn)
    (checkedOptimize_printShape (synthesized_printFacts h henv hwf hn).2) ht]
  intro entry he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hm := (visibleDecls_mem hc p).mp hp
  simp only
  rw [hnames p hm]
  exact compiled_dataNames h henv hwf hn p hm

/-- All widths supplied to SV evaluation can be recovered from the actual
emitted AST, including internal wires. No declaration premise is added. -/
theorem compiled_astWidths {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {sv : SVModule} (htree : emitAstModule (checkedOptimize m) = some sv) :
    astWidths sv = printWidths ((checkedOptimize m).wires ++
      (checkedOptimize m).inputs ++ (checkedOptimize m).outputs) := by
  obtain ⟨hnames, hconsistent⟩ := compiled_declarations h henv hwf hn
  exact astWidths_emitted (printed_printDecls h henv hwf hn)
    (checkedOptimize_printShape (synthesized_printFacts h henv hwf hn).2)
    hnames hconsistent htree

/-- Source-to-emitted-tree correctness with every evaluation width read
from that tree's own declarations. The same-run environment assumption,
positive uniform-width fragment, and in-order semantics remain explicit. -/
theorem compiledFragment_astWidths {declName : Name} {mctx : Meta.Context}
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
          observeUnsignedOutput sv env "out" = some ((denoteFE n sigs fe).val t).toNat := by
  obtain ⟨sv, port, pairs, htree, htext, hitems, hd, hex, hdecl, hout, hsem⟩ :=
    compiledFragment_forward h henv hwf hn
  refine ⟨sv, port, pairs, htree, htext, hitems, hd, hex, hdecl, hout, ?_⟩
  intro dom sigs t mems
  rw [compiled_astWidths h henv hwf hn htree]
  exact hsem sigs t mems

end Tools.ShippingDeclWidths
