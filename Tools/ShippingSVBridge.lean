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
open Tools.ShippingTranslateSoundness Tools.ShippingScalarSoundness

theorem SizedExpr.refs_width {we e n} (h : SizedExpr we e n) :
    ∀ x ∈ Sparkle.IR.Reorder.refsOf e, we x = n := by
  induction h with
  | ref y =>
    intro x hx
    have hxy : x = y := by simpa [Sparkle.IR.Reorder.refsOf] using hx
    exact congrArg we hxy
  | const => simp [Sparkle.IR.Reorder.refsOf]
  | bin op ha hb ia ib =>
    intro x hx
    simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
      List.append_nil, List.mem_append] at hx
    exact hx.elim (ia x) (ib x)

theorem SizedExpr.we_congr {we we' e n} (h : SizedExpr we e n)
    (heq : ∀ x ∈ Sparkle.IR.Reorder.refsOf e, we x = we' x) : SizedExpr we' e n := by
  induction h with
  | ref x => rw [heq x (by simp [Sparkle.IR.Reorder.refsOf])]; exact .ref _
  | const v n => exact .const v n
  | bin op ha hb ia ib =>
    exact .bin op
      (ia fun x hx => heq x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
      (ib fun x hx => heq x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))

theorem SizedExpr.notShl {we e n} (h : SizedExpr we e n) :
    isShlLit e = false ∧ shlOperand e = e := by
  cases h with
  | ref => exact ⟨rfl, rfl⟩
  | const => exact ⟨rfl, rfl⟩
  | bin op => cases op <;> exact ⟨rfl, rfl⟩

theorem SizedExpr.forward {we e n} (h : SizedExpr we e n) (hn : 0 < n)
    (wof : String → Option Nat)
    (hname : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
      Sparkle.Backend.Verilog.sanitizeName x = x ∧ wof x = some (we x)) :
    sf4Check wof we e = true := by
  induction h with
  | ref x =>
    obtain ⟨hs, hw⟩ := hname x (by simp [Sparkle.IR.Reorder.refsOf])
    simp [sf4Check, hs, hw]
  | const => simpa [sf4Check] using hn
  | bin op ha hb ia ib =>
    have ia := ia hn (fun x hx => hname x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have ib := ib hn (fun x hx => hname x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    cases op <;> simp [Binary.operator, sf4Check, ha.width, hb.width,
      (SizedExpr.notShl ha).1, (SizedExpr.notShl ha).2, ia, ib]

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

theorem find_sanitized (ps : List Port) (x : String)
    (hs : ∀ p ∈ ps, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    ps.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) =
      ps.find? (fun p => p.name == x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.find?_cons, hs p (by simp), ih (fun p hp => hs p (by simp [hp]))]

theorem printWidths_wire {m : Sparkle.IR.AST.Module} {x : String} {n : Nat}
    (hn : 0 < n) (hw : Tools.ShippingEntrySoundness.weOf m x = n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    Sparkle.Backend.Verilog.sanitizeName x = x ∧
      printWidths (m.wires ++ m.inputs ++ m.outputs) x = some n := by
  unfold Tools.ShippingEntrySoundness.weOf at hw
  cases hf : m.wires.find? (fun p => p.name == x) with
  | none => simp only [hf] at hw; omega
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpx : p.name = x := by simpa using List.find?_some hf
    have hname : Sparkle.Backend.Verilog.sanitizeName x = x := by
      simpa only [hpx] using hs p hp
    refine ⟨hname, ?_⟩
    simp only [hf] at hw
    unfold printWidths
    rw [List.find?_append, List.find?_append, find_sanitized m.wires x hs, hf]
    obtain ⟨pn, pty⟩ := p
    cases pty <;> simp_all

theorem printWidths_out_of {m : Sparkle.IR.AST.Module} {n : Nat}
    (hout : "out" ∉ m.wires.map (·.name))
    (houts : m.outputs = [{name := "out", ty := .bitVector n}])
    (hi : ∀ p ∈ m.inputs, p ∈ m.wires)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    printWidths (m.wires ++ m.inputs ++ m.outputs) "out" = some n := by
  have hnone : m.wires.find? (fun p => p.name == "out") = none := by
    rw [List.find?_eq_none]
    intro p hp he
    have he : p.name = "out" := by simpa using he
    exact hout (he ▸ List.mem_map_of_mem hp)
  have hinone : m.inputs.find? (fun p => p.name == "out") = none := by
    rw [List.find?_eq_none] at hnone ⊢
    exact fun p hp => hnone p (hi p hp)
  unfold printWidths
  rw [List.find?_append, List.find?_append, find_sanitized m.wires "out" hs,
    find_sanitized m.inputs "out" (fun p hp => hs p (hi p hp)), hnone, hinone,
    houts]
  have ho : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
    simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
  simp [ho]

theorem printWidths_out {m : Sparkle.IR.AST.Module} {n : Nat}
    (hpr : PostReady m n) (hn : 0 < n)
    (hi : ∀ p ∈ m.inputs, p ∈ m.wires)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    printWidths (m.wires ++ m.inputs ++ m.outputs) "out" = some n :=
  printWidths_out_of hpr.2.1 (hpr.2.2.2.1 hn) hi hs

theorem assignsCheck_of_singletons (body : List Stmt) (wof : String → Option Nat) (we : WEnv)
    (hs : ∀ st ∈ body, ∃ l r, st = .assign l r)
    (hc : ∀ l r, Stmt.assign l r ∈ body → assignsCheck wof we [.assign l r] = true) :
    assignsCheck wof we body = true := by
  induction body with
  | nil => rfl
  | cons st body ih =>
    obtain ⟨l, r, rfl⟩ := hs st (by simp)
    have hc0 := hc l r (by simp)
    have hr := ih (fun st h => hs st (by simp [h]))
      (fun l r h => hc l r (by simp [h]))
    simpa only [assignsCheck, hr, Bool.and_true] using hc0

/-- The uniform-width invariant suffices for the complete forward checker;
the output port is looked up separately from internal wires. -/
theorem uniform_forwardCheck {m : Sparkle.IR.AST.Module} {n : Nat}
    (hu : Tools.ShippingPostSoundness.UniformStmts (Tools.ShippingEntrySoundness.weOf m) n m.body)
    (hn : 0 < n)
    (ho : printWidths (m.wires ++ m.inputs ++ m.outputs) "out" = some n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  have hszR : ∀ l r, Stmt.assign l r ∈ m.body →
      SizedExpr (Tools.ShippingEntrySoundness.weOf m) r n := by
    intro l r hm
    obtain ⟨_, _, he, hr, _⟩ := hu _ hm
    cases he
    exact hr
  have hre : ∀ l r, Stmt.assign l r ∈ m.body → ∀ x ∈ Sparkle.IR.Reorder.refsOf r,
      Sparkle.Backend.Verilog.sanitizeName x = x ∧
      printWidths (m.wires ++ m.inputs ++ m.outputs) x = some n ∧
      forwardWidths m x = n := by
    intro l r hm x hx
    have hw := SizedExpr.refs_width (hszR l r hm) x hx
    obtain ⟨hsx, hlookup⟩ := printWidths_wire hn hw hs
    exact ⟨hsx, hlookup, by simp only [forwardWidths, hlookup, Option.getD_some]⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro st hm
    obtain ⟨l, r, rfl, _⟩ := hu st hm
    apply List.all_eq_true.mpr
    intro x hx
    apply beq_iff_eq.mpr
    exact (SizedExpr.refs_width (hszR l r hm) x hx).trans (hre l r hm x hx).2.2.symm
  · apply assignsCheck_of_singletons _ _ _
      (fun st hm => by obtain ⟨l, r, he, _⟩ := hu st hm; exact ⟨l, r, he⟩)
    intro l r hm
    have hsz := SizedExpr.we_congr (hszR l r hm) (fun x hx =>
      (SizedExpr.refs_width (hszR l r hm) x hx).trans (hre l r hm x hx).2.2.symm)
    have hfr := SizedExpr.forward hsz hn (printWidths (m.wires ++ m.inputs ++ m.outputs))
      (fun x hx => ⟨(hre l r hm x hx).1, by rw [(hre l r hm x hx).2.2]; exact (hre l r hm x hx).2.1⟩)
    obtain ⟨l', r', heq, _, hcase⟩ := hu (.assign l r) hm
    cases heq
    have hl : Sparkle.Backend.Verilog.sanitizeName l = l ∧
        printWidths (m.wires ++ m.inputs ++ m.outputs) l = some n := by
      rcases hcase with hl | rfl
      · exact printWidths_wire hn hl hs
      · exact ⟨by simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq],
          ho⟩
    have hwl : forwardWidths m l = n := by
      simp only [forwardWidths, hl.2, Option.getD_some]
    simp only [assignsCheck, hl.1, hl.2, hwl, hsz.width, hfr, beq_self_eq_true, Bool.and_true]

/-- All arithmetic/assignment width conditions follow from the core entry's
invariant. Name stability is separate from lexical identifier legality. -/
theorem postReady_forwardCheck {m : Sparkle.IR.AST.Module} {n : Nat}
    (hpr : PostReady m n) (hn : 0 < n)
    (hi : ∀ p ∈ m.inputs, p ∈ m.wires)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  apply uniform_forwardCheck ?_ hn (printWidths_out hpr hn hi hs) hs
  intro s hm
  obtain ⟨l, r, rfl, hc⟩ := hpr.2.2.1 s hm
  refine ⟨l, r, rfl, hpr.2.2.2.2.2 l r hm, ?_⟩
  rcases hc with ⟨_, hl⟩ | ⟨hl, _⟩
  · exact Or.inl (Tools.ShippingPostSoundness.declWidth_of_mem hpr.1 hl)
  · exact Or.inr hl

/-- On the actual CORE entry, no width-check premise is supplied by the
caller. `synthesized_forwardCheck` below transports this result through
cleanup and checked merging; optimizer selection remains separate. -/
theorem core_forwardCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  obtain ⟨port, _, _, hsem⟩ := fragmentDecl_of_env h henv hwf
  obtain ⟨_, _, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  apply postReady_forwardCheck hpr hn ?_ hs
  intro p hp
  obtain ⟨j, hj, hport, hty, hwire⟩ := hins p hp
  obtain ⟨pn, pty⟩ := p
  simp only at hty
  subst pty
  exact hwire

/-- On the actual synthesis result, including zero-width cleanup and checked
duplicate merging, all forward-check width conditions are derived. The wire
name hypothesis remains explicit; this is still before optimizer selection. -/
theorem synthesized_forwardCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true := by
  obtain ⟨m0, d0, w1, hcore, hm⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨env, hev, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, _, hwire⟩ := Tools.ShippingPostSoundness.postprocess_facts hn hpr hm
  obtain ⟨_, _, ho⟩ := Tools.ShippingPostSoundness.postprocess_sound hn hpr hm hev
  have hsub := Tools.ShippingPostSoundness.postprocess_wires_subset hn hpr hm
  apply uniform_forwardCheck (Tools.ShippingPostSoundness.postprocess_sized hn hpr hm) hn ?_ hs
  apply printWidths_out_of ?_ (ho.trans (hpr.2.2.2.1 hn)) ?_ hs
  · intro hmout
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmout
    exact hpr.2.1 (List.mem_map.mpr ⟨p, hsub p hp, heq⟩)
  · intro p hp
    rw [hi] at hp
    obtain ⟨_, _, _, hty, hpwire⟩ := hins p hp
    obtain ⟨pn, pty⟩ := p
    simp only at hty
    subst pty
    exact hwire pn hpwire

/-- Zero-width cleanup preserves the newly derived sizing invariant: its
body and wire-width environment agree with the core module on this fragment. -/
theorem dropZeroWidth_sized {m : Sparkle.IR.AST.Module} {n : Nat}
    (hpr : PostReady m n) (hn : 0 < n) :
    ∀ l r, Stmt.assign l r ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body →
      SizedExpr (Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) r n := by
  obtain ⟨hb, hw, _⟩ := Tools.ShippingPostSoundness.dropZeroWidth_entry m n hn hpr
  rw [hb, hw]
  exact hpr.2.2.2.2.2

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
