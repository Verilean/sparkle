import Tools.ShippingChecksDesign
import Tools.ShippingWidthTables
import Tools.ShippingTypedExprSoundness

/-! # `seqCheck` from typed statements, and the text conjuncts when the module is shipped as it is (G1)

Pure assembly; nothing here is derived from a run.

* `seqCheck_of_stmts`: `seqCheck wof we body` from its per-statement content
  — for an assignment `l := r`: `sanitizeName l = l`, `wof l = some (we l)`,
  `widthOf we r = we l`, `sf4Check wof we r`; for a register: the same of
  its output and input without the name test; instances are not tested;
  no memory (`seqStmtOkI`).
* `Decl wof x`: `x` is sanitize-stable and declared in the emitter's map.
* `seqCheck_of_typed`: with `we = weOf wof`, the four facts follow from
  `Decl` of the target and of every referenced name and
  `TypedExpr (weOf wof) r (weOf wof l)` — `TypedExpr.width` and the printer
  lemma `TypedExpr.forward`.
* `core_text_same`: conjuncts 2 and 3 of `textCheckI` of the SHIPPED module
  in the case `checkedOptimize b = b` (the two fallback branches), from
  `RunFacts C b` and FOUR hypotheses on `b`:
  `hwn` (wire names sanitize-stable), `hread` (the names of `seqNames b.body`
  are wires), `hA` / `hR` (targets declared and stable, right-hand sides
  typed at the target's emitted width, their names declared and stable).
* `core_designCheck_same`: `designCheck` in that case, with `portsMatchB`
  and the children's check left as they are.

What is NOT proved: `hwn`, `hread`, `hA`, `hR` for the full entry's module
of a machine with calls (docs/parallel/G1-designCheck.md, round 3: which
existing facts they would come from). And the case of an ACCEPTED optimizer
candidate.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingSeqCheckTyped
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingTypedExprSoundness (TypedExpr)

/-- **`seqCheck` from its per-statement content.** -/
theorem seqCheck_of_stmts {wof : String → Option Nat} {we : WEnv} :
    ∀ (body : List Stmt),
      (∀ st ∈ body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true) →
      (∀ l r, Stmt.assign l r ∈ body →
        Sparkle.Backend.Verilog.sanitizeName l = l ∧ wof l = some (we l) ∧
          widthOf we r = we l ∧ Tools.SVParser.EmitSem.sf4Check wof we r = true) →
      (∀ o c rk i iv, Stmt.register o c rk i iv ∈ body →
        wof o = some (we o) ∧ widthOf we i = we o ∧
          Tools.SVParser.EmitSem.sf4Check wof we i = true) →
      Tools.SVParser.EmitSem.seqCheck wof we body = true := by
  intro body
  induction body with
  | nil => intro _ _ _; rfl
  | cons st rest ih =>
    intro hk hA hR
    have ih' := ih (fun s hs => hk s (List.Mem.tail _ hs))
      (fun l r hm => hA l r (List.Mem.tail _ hm))
      (fun o c rk i iv hm => hR o c rk i iv (List.Mem.tail _ hm))
    cases st with
    | assign l r =>
      obtain ⟨h1, h2, h3, h4⟩ := hA l r (List.Mem.head _)
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ih'⟩
    | register o c rk i iv =>
      obtain ⟨h2, h3, h4⟩ := hR o c rk i iv (List.Mem.head _)
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨h2, h3⟩, h4⟩, ih'⟩
    | inst mn iname conns =>
      simp only [Tools.SVParser.EmitSem.seqCheck]
      exact ih'
    | _ =>
      exact absurd (hk _ (List.Mem.head _))
        (by simp [Tools.ShippingHierSVSoundness.seqStmtOkI])

/-- A name the emitter prints as it is and knows the width of. -/
def Decl (wof : String → Option Nat) (x : String) : Prop :=
  Sparkle.Backend.Verilog.sanitizeName x = x ∧ ∃ k, wof x = some k

/-- A declared name's entry is its induced width. -/
theorem wof_weOf {wof : String → Option Nat} {x : String} (h : ∃ k, wof x = some k) :
    wof x = some (Tools.SVParser.EmitSem.weOf wof x) := by
  obtain ⟨k, hk⟩ := h
  simp [Tools.SVParser.EmitSem.weOf, hk]

/-- **`seqCheck` from typed statements over declared, sanitize-stable
names**, at the emitter's induced widths. -/
theorem seqCheck_of_typed {wof : String → Option Nat} (body : List Stmt)
    (hk : ∀ st ∈ body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true)
    (hA : ∀ l r, Stmt.assign l r ∈ body →
      Decl wof l ∧
        TypedExpr (Tools.SVParser.EmitSem.weOf wof) r (Tools.SVParser.EmitSem.weOf wof l) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf r, Decl wof x)
    (hR : ∀ o c rk i iv, Stmt.register o c rk i iv ∈ body →
      (∃ k, wof o = some k) ∧
        TypedExpr (Tools.SVParser.EmitSem.weOf wof) i (Tools.SVParser.EmitSem.weOf wof o) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf i, Decl wof x) :
    Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) body = true :=
  seqCheck_of_stmts body hk
    (fun l r hm => by
      obtain ⟨⟨hs, hd⟩, ht, hr⟩ := hA l r hm
      exact ⟨hs, wof_weOf hd, ht.width,
        ht.forward wof (fun x hx => ⟨(hr x hx).1, wof_weOf (hr x hx).2⟩)⟩)
    (fun o c rk i iv hm => by
      obtain ⟨hd, ht, hr⟩ := hR o c rk i iv hm
      exact ⟨wof_weOf hd, ht.width,
        ht.forward wof (fun x hx => ⟨(hr x hx).1, wof_weOf (hr x hx).2⟩)⟩)

variable {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}

/-- **Conjuncts 2 and 3 of `textCheckI` of the shipped module, when the
module is shipped as it is.** -/
theorem core_text_same (h : Tools.ShippingGuardsSound.RunFacts C b)
    (hsame : checkedOptimize b = b)
    -- (A) on the wires
    (hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    -- (B) the names read are wires
    (hread : ∀ x ∈ Tools.ShippingSeqSVSoundness.seqNames b.body, x ∈ b.wires.map (·.name))
    -- (A), (B), (C) per assignment and per register
    (hA : ∀ l r, Stmt.assign l r ∈ b.body →
      Decl (Tools.ShippingDesignSV.wofOf b) l ∧
        TypedExpr (Tools.ShippingDesignSV.weS b) r (Tools.ShippingDesignSV.weS b l) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf r, Decl (Tools.ShippingDesignSV.wofOf b) x)
    (hR : ∀ o c rk i iv, Stmt.register o c rk i iv ∈ b.body →
      (∃ k, Tools.ShippingDesignSV.wofOf b o = some k) ∧
        TypedExpr (Tools.ShippingDesignSV.weS b) i (Tools.ShippingDesignSV.weS b o) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf i, Decl (Tools.ShippingDesignSV.wofOf b) x) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf (checkedOptimize b))
        (Tools.ShippingDesignSV.weS (checkedOptimize b)) (checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body).all
        (fun x => declWidth (checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (checkedOptimize b) x) = true := by
  rw [hsame]
  exact ⟨seqCheck_of_typed b.body
      (fun st hst => List.all_eq_true.mp
        (Tools.ShippingChecksDesign.seqStmtOkI_of_linkedWF _ h.wfB) st hst) hA hR,
    Tools.ShippingWidthTables.seqNames_widths hwn hread⟩

/-- **`designCheck` of the shipped module when it is shipped as it is**:
the structural conjuncts from the run's facts, conjuncts 2 and 3 from the
typed statements; `portsMatchB` and the children's check as hypotheses. -/
theorem core_designCheck_same (h : Tools.ShippingGuardsSound.RunFacts C b)
    (hsame : checkedOptimize b = b) (n : Nat)
    (hwn : ∀ p ∈ b.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hread : ∀ x ∈ Tools.ShippingSeqSVSoundness.seqNames b.body, x ∈ b.wires.map (·.name))
    (hA : ∀ l r, Stmt.assign l r ∈ b.body →
      Decl (Tools.ShippingDesignSV.wofOf b) l ∧
        TypedExpr (Tools.ShippingDesignSV.weS b) r (Tools.ShippingDesignSV.weS b l) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf r, Decl (Tools.ShippingDesignSV.wofOf b) x)
    (hR : ∀ o c rk i iv, Stmt.register o c rk i iv ∈ b.body →
      (∃ k, Tools.ShippingDesignSV.wofOf b o = some k) ∧
        TypedExpr (Tools.ShippingDesignSV.weS b) i (Tools.ShippingDesignSV.weS b o) ∧
        ∀ x ∈ Sparkle.IR.Reorder.refsOf i, Decl (Tools.ShippingDesignSV.wofOf b) x)
    (hports : Tools.ShippingDesignSV.portsMatchB C b = true)
    (hkids : Tools.ShippingDesignSV.kidsPass C (Tools.ShippingChecksDesign.kidCheck C n)
      b.body = true) :
    Tools.ShippingDesignSV.designCheck C n (checkedOptimize b) = true := by
  obtain ⟨ht, hw⟩ := core_text_same h hsame hwn hread hA hR
  exact Tools.ShippingChecksDesign.core_designCheck_rest h n ht hw
    (by rw [hsame]; exact hports) (by rw [hsame]; exact hkids)

end Tools.ShippingSeqCheckTyped
