import Tools.ShippingPrintEntrySoundness

/-! # Interpreting the assignments in the actual emitted tree

The forward-emission theorem returns `CombStep`s, while the shipping printer
bridge returns an `SVModule`. This file connects those representations before
composing with the source theorem. The source-derived printing invariant is
preserved by optimizer selection. Source inputs construct a bounded initial
environment. Allocated-wire name stability follows from the builder and is
no longer a final-theorem premise. Full lexical and external-tool correctness
are not asserted.
-/
namespace Tools.ShippingSVBridge

open Lean Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingPrintSoundness Tools.ShippingModulePrintSoundness
open Tools.ShippingPrintEntrySoundness Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab Sparkle.IR.OptCheck
open Tools.ShippingTranslateSoundness Tools.ShippingScalarSoundness

theorem sanitizeName_of_clean {s : String} (h : Sparkle.IR.NameHints.Clean s) :
    Sparkle.Backend.Verilog.sanitizeName s = s := by
  have ha : s.all Sparkle.IR.NameHints.charOk = true := by
    simpa [Sparkle.IR.NameHints.Clean, String.all_bool_eq] using h
  simpa [Sparkle.Backend.Verilog.sanitizeName, Sparkle.IR.NameHints.charOk] using
    (if_pos ha : (if s.all Sparkle.IR.NameHints.charOk = true then s else
      s.replace "." "_" |>.replace "-" "_" |>.replace " " "_"
        |>.replace "'" "_prime" |>.replace "#" "") = s)

/-- The name premise follows from actual allocation and the translator's
declaration invariant, through cleanup and checked merging. No source-name
restriction or post-hoc rejection is used. -/
theorem synthesized_names {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
    ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
  obtain ⟨m0, _, _, hcore, hm⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, _, _, hpr, _, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  intro p hp
  exact sanitizeName_of_clean (hpr.2.2.2.2.1.2.2.2 p
    (Tools.ShippingPostSoundness.postprocess_wires_subset hn hpr hm p hp))

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
only output expressions. `compiled_forwardCheck` derives it for the source
fragment through the actual optimizer selection. -/
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

/-- The executable guard recognizes the uniform-width source invariant. -/
theorem printExpr_of_sized {m : Sparkle.IR.AST.Module} {e : Sparkle.IR.AST.Expr} {n : Nat}
    (h : SizedExpr (Tools.ShippingEntrySoundness.weOf m) e n)
    (hr : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
      Sparkle.Backend.Verilog.sanitizeName x = x ∧ Sparkle.IR.PrintCheck.widths m x = some n) :
    Sparkle.IR.PrintCheck.exprCheck m n e = true := by
  induction h with
  | ref x =>
    obtain ⟨hs, hw⟩ := hr x (by simp [Sparkle.IR.Reorder.refsOf])
    simp [Sparkle.IR.PrintCheck.exprCheck, hs, hw]
    rfl
  | const => simp [Sparkle.IR.PrintCheck.exprCheck]
  | bin op ha hb ia ib =>
    have ia := ia (fun x hx => hr x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    have ib := ib (fun x hx => hr x (by simp [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList, hx]))
    cases op <;> simp [Sparkle.IR.PrintCheck.exprCheck, Binary.operator, ia, ib]

theorem printExpr_sound (m : Sparkle.IR.AST.Module) (n : Nat) :
    ∀ e, Sparkle.IR.PrintCheck.exprCheck m n e = true →
      SizedExpr (Tools.ShippingEntrySoundness.weOf m) e n ∧
      (∀ x ∈ Sparkle.IR.Reorder.refsOf e,
        Sparkle.Backend.Verilog.sanitizeName x = x ∧ Sparkle.IR.PrintCheck.widths m x = some n) := by
  intro e
  induction e using Sparkle.IR.PrintCheck.exprCheck.induct with
  | case1 x =>
    intro h
    simp only [Sparkle.IR.PrintCheck.exprCheck, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨?_, ?_⟩
    · have hw : Tools.ShippingEntrySoundness.weOf m x = n := h.2
      simpa only [hw] using SizedExpr.ref (we := Tools.ShippingEntrySoundness.weOf m) x
    · intro y hy
      have he : y = x := by simpa [Sparkle.IR.Reorder.refsOf] using hy
      subst y
      exact h.1
  | case2 v k =>
    intro h
    have hk : k = n := by simpa [Sparkle.IR.PrintCheck.exprCheck] using h
    subst k
    exact ⟨.const v n, by simp [Sparkle.IR.Reorder.refsOf]⟩
  | case3 op a b ia ib =>
    intro h
    simp only [Sparkle.IR.PrintCheck.exprCheck, Bool.and_eq_true] at h
    obtain ⟨ha, hna⟩ := ia h.1.2
    obtain ⟨hb, hnb⟩ := ib h.2
    refine ⟨?_, ?_⟩
    · have hop := h.1.1
      cases op <;> simp_all
      all_goals first | exact SizedExpr.bin .add ha hb | exact SizedExpr.bin .sub ha hb |
        exact SizedExpr.bin .mul ha hb | exact SizedExpr.bin .and ha hb |
        exact SizedExpr.bin .or ha hb | exact SizedExpr.bin .xor ha hb
    · intro x hx
      simp only [Sparkle.IR.Reorder.refsOf, Sparkle.IR.Reorder.refsOf.refsList,
        List.append_nil, List.mem_append] at hx
      exact hx.elim (hna x) (hnb x)
  | case4 e h1 h2 h3 =>
    intro h
    simp only [Sparkle.IR.PrintCheck.exprCheck] at h
    cases h

theorem printCheck_of_uniform {m : Sparkle.IR.AST.Module} {n : Nat}
    (hu : Tools.ShippingPostSoundness.UniformStmts (Tools.ShippingEntrySoundness.weOf m) n m.body)
    (hn : 0 < n)
    (ho : printWidths (m.wires ++ m.inputs ++ m.outputs) "out" = some n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    Sparkle.IR.PrintCheck.moduleCheck m = true := by
  apply List.all_eq_true.mpr
  intro st hm
  obtain ⟨l, e, rfl, he, hl⟩ := hu st hm
  have hlw : Sparkle.Backend.Verilog.sanitizeName l = l ∧
      Sparkle.IR.PrintCheck.widths m l = some n := by
    rcases hl with hl | rfl
    · exact printWidths_wire hn hl hs
    · exact ⟨by simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq], ho⟩
  have hc := printExpr_of_sized he (fun x hx => printWidths_wire hn (SizedExpr.refs_width he x hx) hs)
  simp only [hlw.1, hlw.2, beq_self_eq_true, hc, decide_eq_true hn, Bool.true_and]

theorem printCheck_forward {m : Sparkle.IR.AST.Module}
    (hc : Sparkle.IR.PrintCheck.moduleCheck m = true) : forwardCheck m = true := by
  have hall := List.all_eq_true.mp hc
  have facts : ∀ st ∈ m.body, ∃ l r n, st = .assign l r ∧
      Sparkle.Backend.Verilog.sanitizeName l = l ∧
      printWidths (m.wires ++ m.inputs ++ m.outputs) l = some n ∧ 0 < n ∧
      SizedExpr (Tools.ShippingEntrySoundness.weOf m) r n ∧
      (∀ x ∈ Sparkle.IR.Reorder.refsOf r, Sparkle.Backend.Verilog.sanitizeName x = x ∧
        printWidths (m.wires ++ m.inputs ++ m.outputs) x = some n) := by
    intro st hm
    have hc := hall st hm
    cases st with
    | assign l r =>
      cases hw : Sparkle.IR.PrintCheck.widths m l with
      | none => simp [hw] at hc
      | some n =>
        simp only [hw, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨he, hr⟩ := printExpr_sound m n r hc.2
        exact ⟨l, r, n, rfl, hc.1.1, hw, hc.1.2, he, hr⟩
    | _ => cases hc
  have readWidths : ∀ l r, Stmt.assign l r ∈ m.body →
      ∀ x ∈ Sparkle.IR.Reorder.refsOf r, Sparkle.IR.RegDedup.declWidth m x = forwardWidths m x := by
    intro l r hm x hx
    obtain ⟨_, _, n, heq, _, _, _, he, hr⟩ := facts _ hm
    cases heq
    rw [show forwardWidths m x = n by simp only [forwardWidths, (hr x hx).2, Option.getD_some]]
    exact SizedExpr.refs_width he x hx
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply List.all_eq_true.mpr
    intro st hm
    obtain ⟨l, r, _, rfl, _⟩ := facts st hm
    exact List.all_eq_true.mpr (fun x hx => beq_iff_eq.mpr (readWidths l r hm x hx))
  · apply assignsCheck_of_singletons _ _ _
      (fun st hm => by obtain ⟨l, r, _, h, _⟩ := facts st hm; exact ⟨l, r, h⟩)
    intro l r hm
    obtain ⟨_, _, n, heq, hl, hw, hn, he, hr⟩ := facts _ hm
    cases heq
    have he' := SizedExpr.we_congr he (readWidths l r hm)
    have hf := SizedExpr.forward he' hn (printWidths (m.wires ++ m.inputs ++ m.outputs)) (fun x hx => by
      refine ⟨(hr x hx).1, ?_⟩
      rw [← readWidths l r hm x hx]
      change _ = some (Tools.ShippingEntrySoundness.weOf m x)
      rw [SizedExpr.refs_width he x hx]
      exact (hr x hx).2)
    have hwl : forwardWidths m l = n := by simp only [forwardWidths, hw, Option.getD_some]
    simp only [assignsCheck, hl, hw, hwl, he'.width, hf, beq_self_eq_true, Bool.and_true]

theorem checkedOptimize_printCheck {m : Sparkle.IR.AST.Module}
    (hg : simpleBody m = true) (hc : Sparkle.IR.PrintCheck.moduleCheck m = true) :
    Sparkle.IR.PrintCheck.moduleCheck (checkedOptimize m) = true := by
  unfold checkedOptimize
  simp only [hg, if_true]
  split
  · rename_i ho
    have ho := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ho).2).2
    have ho : Sparkle.IR.PrintCheck.moduleCheck (Sparkle.IR.Optimize.optimizeModule m) = true ∧
        Sparkle.IR.PrintCheck.inputWidthsAgree m (Sparkle.IR.Optimize.optimizeModule m) = true := by simpa [hc] using ho
    exact ho.1
  · exact hc

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
theorem synthesized_printCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    Sparkle.IR.PrintCheck.moduleCheck m = true := by
  obtain ⟨m0, d0, w1, hcore, hm⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨env, hev, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, _, hwire⟩ := Tools.ShippingPostSoundness.postprocess_facts hn hpr hm
  obtain ⟨_, _, ho⟩ := Tools.ShippingPostSoundness.postprocess_sound hn hpr hm hev
  have hsub := Tools.ShippingPostSoundness.postprocess_wires_subset hn hpr hm
  apply printCheck_of_uniform (Tools.ShippingPostSoundness.postprocess_sized hn hpr hm) hn ?_ hs
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

theorem checkedOptimize_inputWidths {m : Sparkle.IR.AST.Module}
    (hg : simpleBody m = true) (hc : Sparkle.IR.PrintCheck.moduleCheck m = true) :
    ∀ p ∈ m.inputs, Sparkle.IR.PrintCheck.widths (checkedOptimize m) p.name =
      Sparkle.IR.PrintCheck.widths m p.name := by
  unfold checkedOptimize
  simp only [hg, if_true]
  split
  · rename_i ho
    have ho := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ho).2).2
    have ho : Sparkle.IR.PrintCheck.moduleCheck (Sparkle.IR.Optimize.optimizeModule m) = true ∧
        Sparkle.IR.PrintCheck.inputWidthsAgree m (Sparkle.IR.Optimize.optimizeModule m) = true := by simpa [hc] using ho
    intro p hp
    exact beq_iff_eq.mp (List.all_eq_true.mp ho.2 p hp)
  · exact fun _ _ => rfl

/-- Input declarations retain the source width through cleanup and either
optimizer branch. Name stability is inherited from the source module's wires. -/
theorem compiled_inputTypes {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    ∀ p ∈ (checkedOptimize m).inputs,
      p.ty = .bitVector n ∧ Sparkle.Backend.Verilog.sanitizeName p.name = p.name := by
  have hg := (synthesized_printFacts h henv hwf hn).2
  obtain ⟨hiO, _⟩ := Tools.ShippingOptSoundness.checkedOptimize_ports hg
  obtain ⟨m0, _, _, hcore, hm⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, _, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, _, hwire⟩ := Tools.ShippingPostSoundness.postprocess_facts hn hpr hm
  intro p hp
  rw [hiO, hi] at hp
  obtain ⟨_, _, _, ht, hpwire⟩ := hins p hp
  exact ⟨ht, hs { name := p.name, ty := .bitVector n } (hwire p.name hpwire)⟩

/-- Read the width from the actual SV input declaration, not from an IR
lookup. This closes the input-port part of the declaration/evaluator boundary. -/
theorem compiled_inputDecls {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    {sv : SVModule} (htree : emitAstModule (checkedOptimize m) = some sv) :
    ∀ x ∈ (checkedOptimize m).inputs.map (·.name),
      ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
        declaredPortWidth sp = some n ∧ sp.isSigned = false := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ht, hname⟩ := compiled_inputTypes h henv hwf hn hs p hp
  simpa only [hname] using emitAstModule_input htree hp ht hn

/-- Every source input has width `n` in the optimized printer lookup,
including unused inputs. The width is derived, not supplied by the caller. -/
theorem compiled_inputWidths {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    ∀ x ∈ (checkedOptimize m).inputs.map (·.name), forwardWidths (checkedOptimize m) x = n := by
  have hg := (synthesized_printFacts h henv hwf hn).2
  have hc := synthesized_printCheck h henv hwf hn hs
  obtain ⟨hiO, _⟩ := Tools.ShippingOptSoundness.checkedOptimize_ports hg
  obtain ⟨m0, _, _, hcore, hm⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads h
  obtain ⟨_, _, _, hsem⟩ := fragmentDecl_of_env hcore henv hwf
  obtain ⟨_, _, _, hpr, hins, _, _⟩ :=
    hsem (dom := Sparkle.Core.Domain.defaultDomain) (fun _ => Sparkle.Core.Signal.Signal.pure 0)
      0 (fun _ _ => 0) (fun _ => 0)
      (fun _ _ _ _ => by show 0 = (0#n : BitVec n).toNat; simp)
  obtain ⟨_, hi, hnd, hwire⟩ := Tools.ShippingPostSoundness.postprocess_facts hn hpr hm
  intro x hx
  rw [hiO] at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have he := checkedOptimize_inputWidths hg hc p hp
  have hp0 : p ∈ m0.inputs := hi ▸ hp
  obtain ⟨_, _, _, _, hpwire⟩ := hins p hp0
  have hw := (printWidths_wire hn (Tools.ShippingPostSoundness.declWidth_of_mem hnd
    (hwire p.name hpwire)) hs).2
  change Sparkle.IR.PrintCheck.widths m p.name = some n at hw
  change (Sparkle.IR.PrintCheck.widths (checkedOptimize m) p.name).getD 0 = n
  rw [he, hw]
  rfl

theorem synthesized_forwardCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck m = true :=
  printCheck_forward (synthesized_printCheck h henv hwf hn hs)

/-- Both optimizer arms preserve the forward condition established by the
source entry. The caller supplies no condition on the optimizer's output. -/
theorem compiled_forwardCheck {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
    forwardCheck (checkedOptimize m) = true :=
  printCheck_forward (checkedOptimize_printCheck (synthesized_printFacts h henv hwf hn).2
    (synthesized_printCheck h henv hwf hn hs))

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
bytes. The final forward check is derived from the source run and optimizer
selection. Wire sanitizer stability and initial width bounds remain explicit;
this is not full SV tool semantics. -/
theorem compiledFragment_forward_with_initial {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name) :
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
  have hc := compiled_forwardCheck h henv hwf hn hs
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

/-- Supply each source input at its allocated port; all other names start
at zero. The finite search makes this environment executable. -/
def inputEnv {n : Nat} (count : Nat) (port : Nat → Option String)
    (values : Nat → BitVec n) : Env := fun x =>
  match (List.range count).find? (fun j => port j == some x) with
  | some j => (values j).toNat
  | none => 0

theorem inputEnv_input {n count : Nat} {port : Nat → Option String}
    (hd : ∀ j j' w, port j = some w → port j' = some w → j = j')
    (values : Nat → BitVec n) {j : Nat} {x : String}
    (hj : j < count) (hp : port j = some x) :
    inputEnv count port values x = (values j).toNat := by
  unfold inputEnv
  cases hf : (List.range count).find? (fun k => port k == some x) with
  | none =>
    have hfalse := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
    exact False.elim (hfalse (by simp [hp]))
  | some k =>
    have hk : port k = some x := by have hb := List.find?_some hf; simpa using hb
    rw [hd k j x hk hp]

theorem inputEnv_bounded {n count : Nat} {port : Nat → Option String}
    (we : WEnv) (values : Nat → BitVec n)
    (hw : ∀ j x, j < count → port j = some x → we x = n) :
    Bounded we (inputEnv count port values) := by
  intro x
  unfold inputEnv
  cases hf : (List.range count).find? (fun k => port k == some x) with
  | none => exact Nat.two_pow_pos _
  | some j =>
    have hj := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have hp : port j = some x := by have hb := List.find?_some hf; simpa using hb
    rw [hw j x hj hp]
    exact (values j).isLt

/-- Source values construct a bounded initial environment for the actual
emitted tree, and every source input has a matching unsigned SV port whose
literal range has width `n`. No declaration-width, forward-check,
initial-environment, boundedness or wire-name premise is supplied. Environment
identity and fragment scope remain explicit; the conclusion uses
in-order SV assignment semantics, not concurrent module semantics. -/
theorem compiledFragment_forward {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w')
    (henv : EnvDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) :
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
      (∀ j x, j < names.length → port j = some x →
        ∃ sp ∈ sv.ports, sp.dir = .input ∧ sp.name = x ∧
          declaredPortWidth sp = some n ∧ sp.isSigned = false) ∧
      ∀ {dom : Sparkle.Core.Domain.DomainConfig}
        (sigs : Nat → Sparkle.Core.Signal.Signal dom (BitVec n)) (t : Nat) (mems : MEnv),
        let initial := inputEnv names.length port (fun j => (sigs j).val t)
        Bounded (forwardWidths o) initial ∧
        ∃ env, evalAssignsSV wof mems pairs initial = some env ∧
          env "out" = ((denoteFE n sigs fe).val t).toNat := by
  have hs := synthesized_names h henv hwf hn
  obtain ⟨sv, port, pairs, htree, htext, hitems, hd, hex, hsem⟩ :=
    compiledFragment_forward_with_initial h henv hwf hn hs
  refine ⟨sv, port, pairs, htree, htext, hitems, hd, hex, ?_, ?_⟩
  · intro j x hj hx
    obtain ⟨x', hx', hmem⟩ := hex j hj
    have heq : x = x' := Option.some.inj (hx.symm.trans hx')
    subst x'
    exact compiled_inputDecls h henv hwf hn hs htree x hmem
  · intro dom sigs t mems
    have hb := inputEnv_bounded (forwardWidths (checkedOptimize m)) (fun j => (sigs j).val t)
      (port := port) (count := names.length) (fun j x hj hp => by
        obtain ⟨x', hp', hx'⟩ := hex j hj
        have heq : x = x' := Option.some.inj (hp.symm.trans hp')
        subst x'
        exact compiled_inputWidths h henv hwf hn hs x hx')
    exact ⟨hb, hsem sigs t mems _ (fun _ _ hj hp => inputEnv_input hd _ hj hp) hb⟩

end Tools.ShippingSVBridge
