import Tools.ShippingCloseLetsRun
import Tools.ShippingMachineCleanup

/-! # The declared width of the wire `closeLets` leaves on `out` (G1, pure)

The closed machine reads every slot's next value and every output off the
wire `core` that remains after the `let` fields: `core[lo + width - 1 : lo]`.
For these part-selects to be typed, `core` must be DECLARED at least
`lo + width` wide. The data check (`MachineData.ok`) bounds the fields by the
width `c` of the core TERM; this file gives the wire's declared width:

* `packLets_width`: the packed term's width is the `let` fields' widths plus
  the core's.
* `spine_width`: on a typed body whose packed wire `w` has the spine
  `SpineW wires body ws w` (one concatenation `{a, b}` per `let` field, `a`
  declared at the field's width `ws[k]`), whatever `letOperands` returns as
  the remaining wire `core` satisfies
  `width w = ws.sum + width core`, and `core` has a positive width.
* `weOf_wire_bw`: a scalar wire with a distinct name is declared at its
  type's `bitWidth`.

No run. UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCoreWidth
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingTypedExprSoundness (TypedExpr)
open Tools.ShippingTypedPostSoundness (TypedStmts)
open Tools.ShippingCloseLetsRun (SpineW)
open Tools.ShippingUnifiedSource

/-- The packed term's width: the `let` fields' widths, then the core's. -/
theorem packLets_width : ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat}
    (core : Term (.bits c)),
    (Tools.ShippingMachineEntry.packLets fs core).1 = (fs.map (·.1)).sum + c
  | [], c, core => by
    show c = ([] : List Nat).sum + c
    simp
  | f :: rest, c, core => by
    have ih := packLets_width rest core
    show f.1 + (Tools.ShippingMachineEntry.packLets rest core).1 =
      (f.1 :: rest.map (·.1)).sum + c
    rw [ih, List.sum_cons]
    omega

/-- **The remaining wire's width.** -/
theorem spine_width {wires : List Port} {body : List Stmt}
    (typed : TypedStmts (wireWidth wires) body) (hout : wireWidth wires "out" = 0) :
    ∀ (ws : List Nat) (ps : List Port) (w : String) (al : List (Port × String)) (core : String),
      SpineW wires body ws w → ps.length = ws.length → 0 < wireWidth wires w →
      letOperands body ps w = some (al, core) →
      wireWidth wires w = ws.sum + wireWidth wires core ∧ 0 < wireWidth wires core
  | [], [], w, al, core, _, _, hpos, h => by
    simp only [letOperands, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, h2⟩ := h
    rw [← h2]
    exact ⟨by simp, hpos⟩
  | m :: ws, p :: ps, w, al, core, hs, hl, hpos, h => by
    obtain ⟨a0, b0, hc0, hw0, hs'⟩ := hs
    unfold letOperands at h
    split at h
    · rename_i a b hc
      split at h
      · rename_i rest core' hr
        have e := Option.some.inj (hc0.symm.trans hc)
        have ea : a0 = a := congrArg Prod.fst e
        have eb : b0 = b := congrArg Prod.snd e
        rw [ea] at hw0
        rw [eb] at hs'
        have hcore : core' = core := congrArg Prod.snd (Option.some.inj h)
        obtain ⟨l, ex, n, heq, ht, hlw⟩ :=
          typed _ (Tools.ShippingMachineClose.concatParts?_mem hc)
        cases heq
        cases ht with
        | cat _ _ ha hb =>
          have hwab : wireWidth wires w = wireWidth wires a + wireWidth wires b := by
            rcases hlw with h1 | h1
            · exact h1
            · rw [h1, hout] at hpos
              exact absurd hpos (Nat.lt_irrefl 0)
          obtain ⟨ih1, ih2⟩ := spine_width typed hout ws ps b rest core' hs'
            (by simpa using hl) hb hr
          rw [← hcore]
          refine ⟨?_, ih2⟩
          rw [List.sum_cons]
          omega
      · cases h
    · cases h
  | [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl

/-- A scalar wire with a distinct name is declared at its type's width. -/
theorem weOf_wire_bw {m : Sparkle.IR.AST.Module} (nd : (m.wires.map (·.name)).Nodup) {p : Port}
    (hty : p.ty = .bit ∨ ∃ n, p.ty = .bitVector n) (hp : p ∈ m.wires) :
    Tools.ShippingEntrySoundness.weOf m p.name = p.ty.bitWidth := by
  have h := Tools.ShippingMachineCleanup.weOf_port nd hp
  rcases hty with e | ⟨n, e⟩
  · rw [e] at h
    rw [e]
    exact h
  · rw [e] at h
    rw [e]
    exact h

end Tools.ShippingCoreWidth
