import Tools.ShippingNoPortsTypedI
import Tools.ShippingDesignSV
import Tools.ShippingHierOptRun
-- BUILT by the integrator: bs1 exit 1 (two parse errors: `by cases he,` read as a multi-target cases -> parenthesised; `| memory ..` alternative -> twelve `_`), bs2 exit 0 (round par/init, base 87874a82).
-- Writing-time guesses: (g1) `simp only [Tools.SVParser.EmitSem.seqCheck] at hc` unfolds one
-- statement of the structural definition; `simp [Tools.SVParser.EmitSem.seqCheck, h] at hc`
-- closes the `false` case by rewriting the `wof l == …` conjunct; (g2) `hc.2` is the recursive
-- conjunct after `simp only [seqCheck, Bool.and_eq_true]` (left-nested `&&`); (g3) memFree
-- unfolds by `simp only [Tools.ConeFold.memFree] at hmf` on a cons; (g4) in `weS_eq_of_sub`
-- the closing `cases pty <;> simp` proves the EQUALITY as it proved `≤` in `weS_le_of_sub`;
-- (g5) `drivesOf` membership split with `List.mem_append`, `List.mem_flatMap`,
-- `List.mem_filterMap`.

/-! # Emitted widths of the names the shipped module drives (round par/init, L3/L4)

* `seqCheck_mem`, `seqCheck_drives` (L3): in a memory-free body accepted by the emitted text's
  check `seqCheck wof we`, every name the body drives (an assignment target or a register) is
  declared at its width: `wof n = some (we n)`.
* `weS_eq_of_sub` (L4): the equality version of `weS_le_of_sub`: a name off the ports that the
  module `o` DECLARES (`wofOf o x = some k`) has, when `o`'s ports are `b`'s and its wires a
  sub-list of `b`'s, `b`'s declared width.
* `weS_driven_checkedOptimize`: both together for the shipped module: a name off the ports that
  `checkedOptimize b` drives has its emitted width equal to `declWidth b`, given the shipped
  module's `designCheck` (the TBW head's `hDesign`) and `b`'s name facts (`wireNames_runMT`).

No fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingNonzeroInitWidths
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck (drivesOf)
open Sparkle.IR.RegDedup (declWidth)

/-- An accepted body declares every assignment target and register at its width. -/
theorem seqCheck_mem {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, Tools.SVParser.EmitSem.seqCheck wof we body = true →
      ∀ st ∈ body,
        (∀ l r, st = .assign l r → wof l = some (we l)) ∧
        (∀ o c rk i iv, st = .register o c rk i iv → wof o = some (we o))
  | [], _, st, hst => by cases hst
  | s0 :: rest, hc, st, hst => by
    cases s0 with
    | assign l r =>
      have h2 : wof l = some (we l) := by
        cases h : (wof l == some (we l)) with
        | true => exact beq_iff_eq.mp h
        | false => simp [Tools.SVParser.EmitSem.seqCheck, h] at hc
      have hrest : Tools.SVParser.EmitSem.seqCheck wof we rest = true := by
        simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
        exact hc.2
      rcases List.mem_cons.mp hst with rfl | h
      · refine ⟨fun l' r' he => ?_, fun o c rk i iv he => by cases he⟩
        cases he
        exact h2
      · exact seqCheck_mem hrest st h
    | register out c rk inp iv =>
      have h2 : wof out = some (we out) := by
        cases h : (wof out == some (we out)) with
        | true => exact beq_iff_eq.mp h
        | false => simp [Tools.SVParser.EmitSem.seqCheck, h] at hc
      have hrest : Tools.SVParser.EmitSem.seqCheck wof we rest = true := by
        simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
        exact hc.2
      rcases List.mem_cons.mp hst with rfl | h
      · refine ⟨fun l' r' he => (by cases he), fun o c' rk' i iv' he => ?_⟩
        cases he
        exact h2
      · exact seqCheck_mem hrest st h
    | inst mn iname conns =>
      have hrest : Tools.SVParser.EmitSem.seqCheck wof we rest = true := by
        simpa only [Tools.SVParser.EmitSem.seqCheck] using hc
      rcases List.mem_cons.mp hst with rfl | h
      · exact ⟨fun l r he => (by cases he), fun o c rk i iv he => by cases he⟩
      · exact seqCheck_mem hrest st h
    | memory nm aw dw ty wa wd wen ra rd cr ew er =>
      have hrest : Tools.SVParser.EmitSem.seqCheck wof we rest = true := by
        simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
        exact hc.2
      rcases List.mem_cons.mp hst with rfl | h
      · exact ⟨fun l r he => (by cases he), fun o c rk i iv he => by cases he⟩
      · exact seqCheck_mem hrest st h

/-- A name a memory-free body drives is an assignment target or a register. -/
theorem drives_cases {body : List Stmt} (hmf : Tools.ConeFold.memFree body) {n : String}
    (hn : n ∈ drivesOf body) :
    (∃ r, Stmt.assign n r ∈ body) ∨ ∃ c rk i iv, Stmt.register n c rk i iv ∈ body := by
  induction body with
  | nil =>
    simp [drivesOf, Sparkle.IR.Reorder.writesOf] at hn
  | cons st rest ih =>
    have hmf' : Tools.ConeFold.memFree rest := by
      cases st <;> first | exact hmf | exact False.elim hmf |
        (simp only [Tools.ConeFold.memFree] at hmf; exact hmf)
    have hsplit : n ∈ Sparkle.IR.Reorder.stmtWrites st ∨ n ∈ drivesOf rest ∨
        (∃ c rk i iv, st = Stmt.register n c rk i iv) := by
      simp only [drivesOf, Sparkle.IR.Reorder.writesOf, List.flatMap_cons, List.mem_append,
        List.filterMap_cons] at hn
      cases st with
      | register o c rk i iv =>
        simp only [List.mem_cons] at hn
        rcases hn with (h | h) | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_append_left _ h))
        · subst h; exact Or.inr (Or.inr ⟨c, rk, i, iv, rfl⟩)
        · exact Or.inr (Or.inl (List.mem_append_right _ h))
      | _ =>
        rcases hn with (h | h) | h
        all_goals first
          | exact Or.inl h
          | exact Or.inr (Or.inl (List.mem_append_left _ h))
          | exact Or.inr (Or.inl (List.mem_append_right _ h))
    rcases hsplit with h | h | ⟨c, rk, i, iv, he⟩
    · cases st with
      | assign l r =>
        simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        exact Or.inl ⟨r, List.mem_cons.mpr (Or.inl rfl)⟩
      | memory _ _ _ _ _ _ _ _ _ _ _ _ => first | exact False.elim hmf | (simp [Tools.ConeFold.memFree] at hmf)
      | _ => simp [Sparkle.IR.Reorder.stmtWrites] at h
    · rcases ih hmf' h with ⟨r, hr⟩ | ⟨c, rk, i, iv, hr⟩
      · exact Or.inl ⟨r, List.mem_cons_of_mem _ hr⟩
      · exact Or.inr ⟨c, rk, i, iv, List.mem_cons_of_mem _ hr⟩
    · subst he
      exact Or.inr ⟨c, rk, i, iv, List.mem_cons.mpr (Or.inl rfl)⟩

/-- **L3**: a name a memory-free accepted body drives is declared at its width. -/
theorem seqCheck_drives {wof : String → Option Nat} {we : WEnv} {body : List Stmt}
    (hc : Tools.SVParser.EmitSem.seqCheck wof we body = true) (hmf : Tools.ConeFold.memFree body)
    {n : String} (hn : n ∈ drivesOf body) : wof n = some (we n) := by
  rcases drives_cases hmf hn with ⟨r, hr⟩ | ⟨c, rk, i, iv, hr⟩
  · exact (seqCheck_mem hc _ hr).1 n r rfl
  · exact (seqCheck_mem hc _ hr).2 n c rk i iv rfl

/-- **L4**: a name off the ports that `o` declares has `b`'s declared width, when `o` has `b`'s
ports and a sub-list of its wires (`b`'s wire names distinct, all names sanitize-stable). -/
theorem weS_eq_of_sub {o b : Module} (hi : o.inputs = b.inputs) (ho : o.outputs = b.outputs)
    (hsub : ∀ p ∈ o.wires, p ∈ b.wires) (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    {x : String} (hxo : x ∉ b.outputs.map (·.name)) (hxi : x ∉ b.inputs.map (·.name))
    {k : Nat} (hk : Tools.ShippingDesignSV.wofOf o x = some k) :
    Tools.ShippingDesignSV.weS o x = declWidth b x := by
  simp only [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  simp only [Tools.ShippingDesignSV.wofOf, Tools.SVParser.RoundtripProof.moduleWof] at hk
  cases hf : (o.wires ++ o.inputs ++ o.outputs).find?
      (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == x) with
  | none => rw [hf] at hk; simp at hk
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpx : Sparkle.Backend.Verilog.sanitizeName p.name = x := by
      have h := List.find?_some hf
      simpa using h
    rw [hi, ho] at hp
    rcases List.mem_append.mp hp with hp' | hpo
    · rcases List.mem_append.mp hp' with hpw | hpi
      · have hpb := hsub p hpw
        have hname : p.name = x :=
          (hs p (List.mem_append_left _ (List.mem_append_left _ hpb))).symm.trans hpx
        have hfd : b.wires.find? (fun q => q.name == x) = some p := by
          rw [← hname]; exact Tools.ShippingEntrySoundness.find?_of_nodup hnd hpb
        simp only [declWidth, hfd]
        obtain ⟨pn, pty⟩ := p
        cases pty <;> simp
      · exact absurd (List.mem_map.mpr ⟨p, hpi,
          (hs p (List.mem_append_left _ (List.mem_append_right _ hpi))).symm.trans hpx⟩) hxi
    · exact absurd (List.mem_map.mpr ⟨p, hpo,
        (hs p (List.mem_append_right _ hpo)).symm.trans hpx⟩) hxo

/-- **A name off the ports that the shipped module drives has its emitted width equal to
`b`'s declared width** (instance modules: `hierGate`; the shipped module's `designCheck`). -/
theorem weS_driven_checkedOptimize {ms : List Module} {b : Module}
    (hgate : Sparkle.IR.RefineCheck.hierGate b = true)
    (hnd : (b.wires.map (·.name)).Nodup)
    (hs : ∀ p ∈ b.wires ++ b.inputs ++ b.outputs,
      Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hdc : Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap ms) 0
      (Sparkle.IR.OptCheck.checkedOptimize b) = true)
    {x : String} (hxo : x ∉ b.outputs.map (·.name)) (hxi : x ∉ b.inputs.map (·.name))
    (hx : x ∈ drivesOf (Sparkle.IR.OptCheck.checkedOptimize b).body) :
    Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x = declWidth b x := by
  have htc : Tools.ShippingDesignSV.textCheckI (Tools.ShippingMachineLinked.childMap ms)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true := by
    have h := hdc
    simp only [Tools.ShippingDesignSV.designCheck, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨-, hsc, -, hwf, -⟩ := Tools.ShippingDesignSV.textCheckI_sound htc
  have hmf := Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf
  have hk := seqCheck_drives hsc hmf hx
  obtain ⟨hi, ho, hsub⟩ := Tools.ShippingNoPortsTypedI.checkedOptimize_ports_wires hgate
  exact weS_eq_of_sub hi ho hsub hnd hs hxo hxi hk

end Tools.ShippingNonzeroInitWidths
