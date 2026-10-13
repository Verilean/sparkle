import Tools.ShippingMachineEntry
import Tools.ShippingReflectCtx

variable {tenv : Lean.Environment}

/-! # What `MachineCloses` asks of a shape with `let`s

`MachineCloses` says a run of the machine synthesis does not return `none`.
For a shape WITHOUT calls that is one thing only: `closeLets` accepts the
transition module the certified harness produced
(`machineCloses_noCalls_iff`). And `closeLets` accepts a module iff six
conditions hold of it (`closeLets_isSome_iff`):

1. the body ends in `assign out = w`;
2. from `w`, one two-operand concatenation per `let` port (`letOperands`);
3. each operand wire is declared at its port's width, the width is positive,
   and neither name is `out`;
4. no `let` port is driven by the transition;
5. the wire left after the last `let` is not `out`;
6. the closed statements — every alias right after its operand's driver —
   are in dependency order (`assignmentOrderCheck`).

These are properties of the module the RUN produced. Which of them follow
from a successful harness run, and which are not derived, is recorded in
`docs/ShippingCompiler-TrustBase.md`; nothing here assumes any of them. -/
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry

namespace Tools.ShippingCloseLetsSplit

/-- The statements of a let-closed transition: the aliases of undriven operand
wires, the body with each alias after its operand's driver, the final `out`. -/
def closedBody (t : Sparkle.IR.AST.Module) (aliases : List (Port × String)) (core : String) : List Stmt :=
  frontAliases aliases t.body.dropLast ++ insertAliases aliases t.body.dropLast ++
    [.assign "out" (.ref core)]

/-- **What `closeLets` asks, exactly.** With `let`s (`K ≠ 0`) it returns a
module iff: (1) the body ends in `assign out = w`; (2) from `w`, one
two-operand concatenation per `let` port; (3) each operand wire is declared
at its port's width, which is positive, and neither is `out`; (4) no `let`
port is driven by the transition; (5) the remaining wire is not `out`; (6)
the closed statements are in dependency order. -/
theorem closeLets_isSome_iff {K : Nat} {t : Sparkle.IR.AST.Module} (hK : K ≠ 0) :
    (closeLets K t).isSome = true ↔
    ∃ w aliases core, packedWire? t.body = some w ∧
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (aliases, core) ∧
      (∀ pa ∈ aliases, wireWidth t.wires pa.2 = pa.1.ty.bitWidth ∧ 0 < pa.1.ty.bitWidth ∧
        pa.1.name ≠ "out" ∧ pa.2 ≠ "out") ∧
      (∀ pa ∈ aliases, pa.1.name ∉ Sparkle.IR.Reorder.writesOf t.body) ∧
      core ≠ "out" ∧
      Sparkle.IR.OptCheck.assignmentOrderCheck (closedBody t aliases core) = true := by
  constructor
  · intro h
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp h
    unfold closeLets at ht'
    simp only [hK, if_false] at ht'
    split at ht'
    · cases ht'
    · rename_i w hpw
      split at ht'
      · cases ht'
      · rename_i aliases core hops
        split at ht'
        · rename_i hchk
          simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
            decide_eq_true_eq, Bool.not_eq_true'] at hchk
          refine ⟨w, aliases, core, hpw, hops, fun pa hpa => ?_, fun pa hpa => ?_, hchk.1.2, ?_⟩
          · have := hchk.1.1 pa hpa
            exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2⟩
          · have := (hchk.1.1 pa hpa).2
            simpa using this
          · unfold closedBody; exact hchk.2
        · cases ht'
  · rintro ⟨w, aliases, core, hpw, hops, h1, h2, h3, h4⟩
    unfold closedBody at h4
    have hchk : (aliases.all (fun pa => wireWidth t.wires pa.2 == pa.1.ty.bitWidth &&
          decide (0 < pa.1.ty.bitWidth) && pa.1.name != "out" && pa.2 != "out" &&
          !(Sparkle.IR.Reorder.writesOf t.body).contains pa.1.name) &&
        core != "out" &&
        Sparkle.IR.OptCheck.assignmentOrderCheck (frontAliases aliases t.body.dropLast ++
          insertAliases aliases t.body.dropLast ++ [.assign "out" (.ref core)])) = true := by
      simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
        decide_eq_true_eq, Bool.not_eq_true']
      refine ⟨⟨fun pa hpa => ?_, h3⟩, h4⟩
      obtain ⟨a1, a2, a3, a4⟩ := h1 pa hpa
      exact ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, by simpa using h2 pa hpa⟩
    unfold closeLets
    simp only [hK, if_false, hpw, hops]
    rw [if_pos hchk]; rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`MachineCloses` of a shape without calls is about the harness' outputs.**
It holds in a pair of contexts iff `closeLets` accepts the transition module
of every run of the certified harness there. Nothing else is in it. -/
theorem machineCloses_noCalls_iff {declName : Name} {shape : MachineShape}
    (hi : shape.insts = []) :
    MachineCloses mctx mref cctx cref declName shape ↔
    ∀ {tenv : Lean.Environment} (logProf : String → IO Unit) w t d w',
      RunsTo (synthesizeMixedCertified (fun e hint top named => translateExprToWire tenv e hint top named)
        logProf declName shape.binders shape.body) mctx mref cctx cref w (t, d) w' →
      (closeLets shape.layout.lets t).isSome = true := by
  constructor
  · intro hc tenv logProf w t d w' hr
    cases hcl : closeLets shape.layout.lets t with
    | some t' => rfl
    | none =>
      have hrun : RunsTo (synthesizeMachineCertified
          (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName shape)
          mctx mref cctx cref w none w' := by
        unfold synthesizeMachineCertified
        refine Tools.ShippingReflectCtx.RunsTo.bind_intro hr ?_
        simp only [hcl]
        rfl
      exact absurd rfl (hc logProf w none w' hrun)
  · intro h tenv logProf w r w' hr
    unfold synthesizeMachineCertified at hr
    obtain ⟨⟨t, d⟩, w1, h1, hr⟩ := RunsTo.bind hr
    dsimp only at hr
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h logProf w t d w1 h1)
    rw [ht', hi] at hr
    have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _

/-! ## Condition (2) as a spine

What the translator would have to leave for condition (2), stated on the body
alone: these are the pure facts a spine postcondition of the concat arm
composes with (`Spine.emit` for a freshly driven wire, `Spine.append` for
everything emitted afterwards). The induction over the translator that
supplies `Spine` for the wire it returns — through the validated cache too —
is NOT here. -/

/-- From `w`, `n` links of two-operand concatenations in `body`: the shape
`letOperands` walks, one link per `let` port. -/
def Spine (body : List Stmt) : Nat → String → Prop
  | 0, _ => True
  | n + 1, w => ∃ a b, concatParts? body w = some (a, b) ∧ Spine body n b

/-- **Condition (2) is the spine.** `letOperands` succeeds on `ps` from `w`
iff `body` has a spine of `ps.length` links from `w`. -/
theorem letOperands_isSome_iff (body : List Stmt) :
    ∀ (ps : List Port) (w : String),
      (letOperands body ps w).isSome = true ↔ Spine body ps.length w
  | [], w => by simp [letOperands, Spine]
  | p :: ps, w => by
    unfold letOperands
    simp only [List.length_cons, Spine]
    cases hc : concatParts? body w with
    | none => simp
    | some ab =>
      obtain ⟨a, b⟩ := ab
      have ih := letOperands_isSome_iff body ps b
      cases hr : letOperands body ps b with
      | none =>
        rw [hr] at ih
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at ih
        constructor
        · intro h; simp [hr] at h
        · rintro ⟨a', b', h, hs⟩
          cases h
          exact absurd hs ih
      | some rc =>
        rw [hr] at ih
        simp only [Option.isSome_some, true_iff] at ih
        exact ⟨fun _ => ⟨a, b, rfl, ih⟩, fun _ => by simp [hr]⟩

/-- A link found in a body is still the link after more statements. -/
theorem concatParts?_append {body : List Stmt} {w a b : String} (more : List Stmt)
    (h : concatParts? body w = some (a, b)) : concatParts? (body ++ more) w = some (a, b) := by
  unfold concatParts? at h ⊢
  rw [List.findSome?_append, h]
  rfl

/-- A spine survives appended statements. -/
theorem Spine.append {body : List Stmt} (more : List Stmt) :
    ∀ {n : Nat} {w : String}, Spine body n w → Spine (body ++ more) n w
  | 0, _, _ => trivial
  | _ + 1, _, ⟨a, b, h, hs⟩ => ⟨a, b, concatParts?_append more h, hs.append more⟩

/-- No statement of `body` is a two-operand concatenation driving `w`. -/
def NoConcat (body : List Stmt) (w : String) : Prop := concatParts? body w = none

/-- **One link, as the concat arm emits it**: after a body in which `w` has
no concatenation driver (a fresh wire), `assign w = {a, b}` is `w`'s link. -/
theorem concatParts?_emit {body : List Stmt} {w a b : String} (h : NoConcat body w) :
    concatParts? (body ++ [.assign w (.concat [.ref a, .ref b])]) w = some (a, b) := by
  unfold NoConcat concatParts? at *
  rw [List.findSome?_append, h]
  simp

/-- The spine of a wire the concat arm has just driven, from its right
operand's spine. -/
theorem Spine.emit {body : List Stmt} {w a b : String} {n : Nat} (h : NoConcat body w)
    (hb : Spine body n b) :
    Spine (body ++ [.assign w (.concat [.ref a, .ref b])]) (n + 1) w :=
  ⟨a, b, concatParts?_emit h, hb.append _⟩


end Tools.ShippingCloseLetsSplit
