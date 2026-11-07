import Tools.ShippingGen5DataOf
import Tools.ShippingFGCircuitCover
import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot S3b2 (route B), unit 1: the REAL `dataOfAt` check as a Bool function with a structural comparison, and its soundness onto `RootReader`.
-- Nothing here is a copy of the reader: `rootReaderB` calls `dataOfAt` / `machineShape?` / `entry₀` themselves.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §53.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3b2Reader
open Lean Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingGen5DataOf Tools.ShippingGen5DataOfPure Tools.ShippingGen5Acc
open Tools.ShippingFGCircuitCover (RootReader)

local instance : DecidableEq Expr := fun a b => Sparkle.Compiler.ExprDecEq.exprDecEq a b

/-! ## the verification fuel `lvl₀`

A concrete, deterministic fuel setting of THIS check (not "the level an existing entry fixes"): the `readN` level of a body is the nesting depth of the body (`Expr.approxDepth`, cached, saturating at 255).  The same `lvl₀` is used for the root's `hchk`, the two children's `RootReader` and the conclusion's `GPt`. -/
def lvl₀ : Lean.Expr → Nat := fun e => e.approxDepth.toNat

/-! ## the structural comparison of `MachineData` (not a `LawfulBEq`: only `mdBeq a b = true → a = b`) -/

def layoutBeq (a b : Layout) : Bool :=
  decide (a.slots = b.slots) && decide (a.outs = b.outs) && decide (a.resetKind = b.resetKind) && a.lets == b.lets

theorem layoutBeq_eq {a b : Layout} (h : layoutBeq a b = true) : a = b := by
  obtain ⟨s, o, r, l⟩ := a
  obtain ⟨s', o', r', l'⟩ := b
  simp only [layoutBeq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  subst h1 h2 h3 h4
  rfl

def shapeBeq (a b : MachineShape) : Bool :=
  decide (a.binders = b.binders) && decide (a.body = b.body) && layoutBeq a.layout b.layout &&
  decide (a.runs = b.runs) && decide (a.insts = b.insts) && decide (a.loops = b.loops) &&
  decide (a.instFields = b.instFields) && decide (a.instOrigins = b.instOrigins)

theorem shapeBeq_eq {a b : MachineShape} (h : shapeBeq a b = true) : a = b := by
  obtain ⟨b1, bo, la, ru, ins, lo, inf, ino⟩ := a
  obtain ⟨b1', bo', la', ru', ins', lo', inf', ino'⟩ := b
  simp only [shapeBeq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have h3' := layoutBeq_eq h3
  subst h1 h2 h3' h4 h5 h6 h7 h8
  rfl

/-- the typed terms of two lists, in order, each with its sort AND its term -/
def anysBeq : List (Σ s : SType, Term s) → List (Σ s : SType, Term s) → Bool
  | [], [] => true
  | a :: xs, b :: ys => anyBeq a b && anysBeq xs ys
  | _, _ => false

theorem anysBeq_eq : ∀ {a b : List (Σ s : SType, Term s)}, anysBeq a b = true → a = b
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [anysBeq, Bool.and_eq_true] at h
    rw [anyBeq_eq h.1, anysBeq_eq h.2]
  | [], _ :: _, h => by simp [anysBeq] at h
  | _ :: _, [], h => by simp [anysBeq] at h

/-- the `Terms` of two states, componentwise (sort and term) -/
def termsBeq : {ss ss' : List SType} → Terms ss → Terms ss' → Bool
  | _, _, .nil, .nil => true
  | _, _, .cons a xs, .cons b ys => termBeq a b && termsBeq xs ys
  | _, _, _, _ => false

theorem termsBeq_sound : ∀ {ss ss' : List SType} (a : Terms ss) (b : Terms ss'), termsBeq a b = true → ss = ss' ∧ HEq a b
  | _, _, .nil, .nil, _ => ⟨rfl, HEq.rfl⟩
  | _, _, .cons a xs, .cons b ys, h => by
    simp only [termsBeq, Bool.and_eq_true] at h
    obtain ⟨hs, hab⟩ := termBeq_sound a b h.1
    obtain ⟨hss, hbs⟩ := termsBeq_sound xs ys h.2
    subst hs hss
    exact ⟨rfl, heq_of_eq (by rw [eq_of_heq hab, eq_of_heq hbs])⟩
  | _, _, .nil, .cons _ _, h => by simp [termsBeq] at h
  | _, _, .cons _ _, .nil, h => by simp [termsBeq] at h

def mdBeq (a b : MachineData) : Bool :=
  shapeBeq a.shape b.shape && a.nIn == b.nIn && decide (a.dom = b.dom) &&
  decide (a.bposL = b.bposL) && decide (a.vposL = b.vposL) && decide (a.vwL = b.vwL) &&
  decide (a.ss = b.ss) && anysBeq a.ls b.ls && anysBeq a.outs b.outs && termsBeq a.nexts b.nexts

theorem mdBeq_eq {a b : MachineData} (h : mdBeq a b = true) : a = b := by
  obtain ⟨sh, nIn, dom, bp, vp, vw, ss, ls, outs, nx⟩ := a
  obtain ⟨sh', nIn', dom', bp', vp', vw', ss', ls', outs', nx'⟩ := b
  simp only [mdBeq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have h1' := shapeBeq_eq h1
  have h8' := anysBeq_eq h8
  have h9' := anysBeq_eq h9
  subst h1' h2 h3 h4 h5 h6 h7 h8' h9'
  have := eq_of_heq (termsBeq_sound nx nx' h10).2
  subst this
  rfl

/-! ## the check: the real `dataOfAt` at `lvl₀` against the expected `MachineData` -/

/-- `RootReader lvl env X d` as a Bool: `entry₀` finds the entry constant, `machineShape?` gives `d.shape`, and the REAL `dataOfAt lvl` on it returns a `MachineData` structurally equal to `d` -/
def rootReaderB (lvl : Lean.Expr → Nat) (env : Environment) (X : Name) (d : MachineData) : Bool :=
  match entry₀ env X with
  | none => false
  | some E =>
    match machineShape? false [] E (structEnv env) with
    | none => false
    | some s =>
      shapeBeq s d.shape &&
        (match dataOfAt lvl E (structEnv env) d.shape with
         | none => false
         | some d' => mdBeq d' d)

theorem rootReaderB_sound {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {d : MachineData}
    (h : rootReaderB lvl env X d = true) : RootReader lvl env X d := by
  unfold rootReaderB at h
  split at h
  · cases h
  · rename_i E hE
    split at h
    · cases h
    · rename_i s hs
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hsd : s = d.shape := shapeBeq_eq h1
      split at h2
      · cases h2
      · rename_i d' hd'
        have : d' = d := mdBeq_eq h2
        subst this
        refine ⟨E, hE, ?_, hd'⟩
        rw [hs, hsd]

end Tools.ShippingFGCircuitS3b2Reader

#print axioms Tools.ShippingFGCircuitS3b2Reader.mdBeq_eq
#print axioms Tools.ShippingFGCircuitS3b2Reader.rootReaderB_sound
