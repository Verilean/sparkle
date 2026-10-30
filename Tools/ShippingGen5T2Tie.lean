import Tools.ShippingGen5T2Dec
import Tools.ShippingMachineCausal
set_option autoImplicit false
-- Built: g5tt-36beb7dc (clean snapshot, exit 0, standard axioms); issue `sparkle-gen5-t2-tie`. No sorry / axiom /
-- S1 combined: re-elaborated at 02e828fc in s1c-02e828fc (clean, exit 0, standard axioms).
-- native_decide.

/-! # T2-POSENC, T2-FIELD (standalone) and T2-TIE / T2-STEP (CONDITIONAL on named D-GEN units)

Issue `sparkle-gen5-t2-tie`. Design-to-code of scripts/gen5/T2COVER_FREEZE.md rev2 §1 (E1, T2-FIELD), §3 (T2-STEP)
and §5 (units T2-POSENC, T2-FIELD, T2-TIE, T2-STEP), approved as design only at `par/gen5-t2` c398021c, with the D-GEN
objects of scripts/gen5/DGEN_FREEZE.md rev2 (`ClosingRun`, `genSem`, `genP`, `GenData`) NOT BUILT.

**This file is CONDITIONAL on unbuilt D-GEN units. It is NOT the FG, NOT M5, and changes no FG premise.** The
statements fall in two classes:

* **Unconditional (over existing definitions only):**
  - T2-POSENC: `SigAt` / `OutRange` (the shape of a call-result signal at a binder position, and its range),
    `posEnc_of_sigAt` (`posEnc` decodes such a signal back to the stream), the `extendBits` / `extendBools` chain
    lemmas `sigAt_extendBits_self`/`_ne`, `sigAt_extendBools_self`/`_ne` (the generator's placement,
    Tools/ShippingMachineCommand.lean `combCallsProof`), and the package form `posEnc_callPos`;
  - T2-FIELD: `childRunN_outputs` (the output shape, first conjunct of either `ChildRunN` branch), `FieldRowAt` (the
    per-call field row: one output for a one-output parent, the call's field among the child module's outputs for a
    group parent), `fieldRow_one_of_callStmt` (the one-output row from the run's `CallStmt`), `callField_of_outputs`,
    and the per-`i` `callField_at` from the served child's `ShipsRes` (the CHILDREN's IH; never the current parent's
    `T1Hyp.dec`; no `Nonempty ι`: `i` is an argument, used after `intro i`).
* **Conditional (explicit hypotheses named after the D-GEN / M3 units that are to supply them):**
  - T2-TIE: `CallTie`, `callTie_of_dgen` (on `hT2_FIELD`, `hDG_SEM`, `hDG_SEM_range`), `callTie_of_served` (the E1
    shape: on `hDG_GENP` (callee package), `hDG_CLOSINGRUN` (the served result, its design containment and the field
    row, from `ClosingRun.shared`), `hDG_SEM`, `hDG_SEM_range`), `hPointG_of_callTie`;
  - T2-STEP: `callDec_of_callTie` (on `hG_DATA_CALL_*`, M3), `stepDec_of_ties` (StepStmt's per-call decoding premise,
    on `hDG_PKGASSIGN`, `hT2_TIE`, `hG_DATA_CALL_*`, `hG_MEMCALLS`).

**Open (not supplied here):** every `hDG_*` hypothesis (DG-SEM, DG-GENP, DG-PKGASSIGN, DG-CLOSINGRUN); the GROUP field
row (`connsG`'s field name is `instFields[k]` and is an output of the served module; T2COVER rev2 §1 "What is
missing"); `hDG_SEM_range` (see the note at `CallOutRange`: the callee output must lie in the range of the call's
binder kind, which DGEN rev2 does not name as a row); `hG_DATA_CALL_*` (M3); DG-HPOINT (the ∀-ordinary-call form over
`ClosingRun`) and the final assembly closure audit (T2-AUDIT) remain. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## T2-POSENC (unconditional) -/

/-- The call-result signal at binder position `pos` carries the stream `f`, by binder kind: a bit vector of width
`w` is `BitVec.ofNat w (f τ)`, a Bool is `f τ != 0`; a domain position carries no call result. -/
def SigAt {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos : Nat) : Sparkle.Compiler.Elab.MixedGateBinder → (Nat → Nat) → Prop
  | .bits w, f => ∀ τ, (bits pos w).val τ = BitVec.ofNat w (f τ)
  | .bool, f => ∀ τ, (bools pos).val τ = (f τ != 0)
  | .domain, _ => False

/-- The stream `f` lies in the range of binder kind `κ`. -/
def OutRange : Sparkle.Compiler.Elab.MixedGateBinder → (Nat → Nat) → Prop
  | .bits w, f => ∀ τ, f τ < 2 ^ w
  | .bool, f => ∀ τ, f τ < 2
  | .domain, _ => True

theorem encodeBool_bne_of_lt {x : Nat} (h : x < 2) :
    Tools.ShippingMuxLoweringSoundness.encodeBool (x != 0) = x := by
  rcases x with _ | _ | x
  · first | rfl | decide | simp [Tools.ShippingMuxLoweringSoundness.encodeBool]
  · first | rfl | decide | simp [Tools.ShippingMuxLoweringSoundness.encodeBool]
  · exact absurd h (by omega)

/-- **T2-POSENC core**: `posEnc` at `pos` decodes a `SigAt` signal back to its in-range stream. -/
theorem posEnc_of_sigAt {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos : Nat) (κ : Sparkle.Compiler.Elab.MixedGateBinder)
    (f : Nat → Nat) (hs : SigAt bools bits pos κ f) (hr : OutRange κ f) :
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ) (fun r n => (bits r n).val τ) pos κ = f τ := by
  intro τ
  cases κ with
  | domain => exact False.elim hs
  | bool =>
    have h1 : (bools pos).val τ = (f τ != 0) := hs τ
    have h2 : f τ < 2 := hr τ
    show Tools.ShippingMuxLoweringSoundness.encodeBool ((bools pos).val τ) = f τ
    rw [h1]
    exact encodeBool_bne_of_lt h2
  | bits w =>
    have h1 : (bits pos w).val τ = BitVec.ofNat w (f τ) := hs τ
    have h2 : f τ < 2 ^ w := hr τ
    show ((bits pos w).val τ).toNat = f τ
    rw [h1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h2

/-- The generator's bit-vector placement at `pos` (`extendBits … pos w sig`) is a `SigAt` signal. -/
theorem sigAt_extendBits_self {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos w : Nat) (f : Nat → Nat) :
    SigAt bools (Tools.ShippingMachineAuto.extendBits bits pos w ⟨fun τ => BitVec.ofNat w (f τ)⟩) pos (.bits w) f := by
  intro τ
  exact congrArg (fun s : Signal D (BitVec w) => s.val τ)
    (Tools.ShippingMachineCausal.extendBits_self D bits pos w ⟨fun τ => BitVec.ofNat w (f τ)⟩)

/-- The generator's Bool placement at `pos` (`extendBools … pos sig`) is a `SigAt` signal. -/
theorem sigAt_extendBools_self {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos : Nat) (f : Nat → Nat) :
    SigAt (Tools.ShippingMachineCausal.extendBools bools pos ⟨fun τ => f τ != 0⟩) bits pos .bool f := by
  intro τ
  exact congrArg (fun s : Signal D Bool => s.val τ)
    (Tools.ShippingMachineCausal.extendBools_self D bools pos ⟨fun τ => f τ != 0⟩)

/-- A bit-vector placement at another position `pos'` does not change `SigAt` at `pos` (any kind). -/
theorem sigAt_extendBits_ne {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) {pos pos' w : Nat} (sig : Signal D (BitVec w))
    (h : pos ≠ pos') (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat) :
    SigAt bools (Tools.ShippingMachineAuto.extendBits bits pos' w sig) pos κ f ↔ SigAt bools bits pos κ f := by
  cases κ with
  | domain => exact Iff.rfl
  | bool => exact Iff.rfl
  | bits n =>
    have e := Tools.ShippingMachineCausal.extendBits_ne D bits pos' w sig pos n h
    constructor
    · intro hs τ
      have h1 := hs τ
      rw [e] at h1
      exact h1
    · intro hs τ
      have h1 := hs τ
      rw [e]
      exact h1

/-- A Bool placement at another position `pos'` does not change `SigAt` at `pos` (any kind). -/
theorem sigAt_extendBools_ne {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) {pos pos' : Nat} (sig : Signal D Bool)
    (h : pos ≠ pos') (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat) :
    SigAt (Tools.ShippingMachineCausal.extendBools bools pos' sig) bits pos κ f ↔ SigAt bools bits pos κ f := by
  cases κ with
  | domain => exact Iff.rfl
  | bits n => exact Iff.rfl
  | bool =>
    have e := Tools.ShippingMachineCausal.extendBools_ne D bools pos' sig pos h
    constructor
    · intro hs τ
      have h1 := hs τ
      rw [e] at h1
      exact h1
    · intro hs τ
      have h1 := hs τ
      rw [e]
      exact h1

/-- **T2-POSENC, package form**: at call `k`'s position `p.kD + k` and its binder kind, a `SigAt` signal with an
in-range stream gives exactly `CallOutF`'s / `CallDec`'s `posEnc` conjunct. -/
theorem posEnc_callPos (p : Pkg ι dom) (k : Nat) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (f : Nat → Nat)
    (hs : SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f)
    (hr : OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f) :
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
      (fun r n => (p.extS i bools bits r n).val τ)
      (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ :=
  posEnc_of_sigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k) _ f hs hr

/-! ## T2-FIELD (unconditional; per `i`) -/

/-- The output shape of a child run (the first conjunct of either branch of `ChildRunN`). -/
theorem childRunN_outputs {children} {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)} {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)} :
    ChildRunN children dsn n mc bsC outsC S →
      mc.outputs = outsC.map (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) := by
  intro h
  rcases h with h | h
  · first | exact h.1 | simpa using h.1
  · first | exact h.1 | simpa using h.1

/-- **The per-call field row** on the served child module `mc` (mirrors `CallField`'s exact `if`): a one-output
parent's call reads a module with exactly one output; a group parent's call `k` reads the field `instFields[k]`,
which is one of `mc`'s outputs. The one-output row is supplied from the run's `CallStmt` (`fieldRow_one_of_callStmt`);
the GROUP row (from `connsG` in `ServedGP`) is OPEN (T2COVER rev2 §1 "What is missing"). -/
def FieldRowAt (p : Pkg ι dom) (k : Nat) (mc : Sparkle.IR.AST.Module) : Prop :=
  if p.d.shape.instFields = [] then ∃ outP, mc.outputs = [outP]
  else p.d.shape.instFields.getD k "" ∈ mc.outputs.map (·.name)

/-- One-output parents: the run's call statement (`CallStmt`, as served by `Served1P`) gives the field row. -/
theorem fieldRow_one_of_callStmt (p : Pkg ι dom) (k : Nat) {nIn kI n : Nat} {portNames : List String}
    {args : List Nat} {mc : Sparkle.IR.AST.Module} {st : Sparkle.IR.AST.Stmt}
    (h1 : p.d.shape.instFields = [])
    (hst : Tools.ShippingMachineInst.CallStmt nIn kI n portNames k args mc st) : FieldRowAt p k mc := by
  unfold FieldRowAt
  rw [if_pos h1]
  obtain ⟨_, _, outP, _, _, _, hout, -⟩ := hst
  exact ⟨outP, hout⟩

theorem single_of_map_eq {α β : Type} (f : α → β) : ∀ (L : List α) (b : β), [b] = L.map f → ∃ a, L = [a]
  | [], _, h => by simp at h
  | [a], _, _ => ⟨a, rfl⟩
  | _ :: _ :: _, _, h => by simp at h

/-- The field row on a module whose outputs are `q`'s layout outputs gives `CallField`'s witnesses. -/
theorem callField_of_outputs (p q : Pkg ι dom) (k : Nat) (mc : Sparkle.IR.AST.Module)
    (hout : mc.outputs = q.d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hrow : FieldRowAt p k mc) :
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o := by
  unfold FieldRowAt at hrow
  by_cases h1 : p.d.shape.instFields = []
  · rw [if_pos h1] at hrow
    obtain ⟨outP, hP⟩ := hrow
    rw [hP] at hout
    obtain ⟨o, ho⟩ := single_of_map_eq _ _ _ hout
    exact ⟨0, o, by simp [ho], (callField_one (q := q) (k := k) (o := o) h1).mpr ho⟩
  · rw [if_neg h1] at hrow
    rw [hout] at hrow
    obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hrow
    obtain ⟨o, hoMem, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.mp hoMem
    exact ⟨k', o, hk', (callField_group (q := q) (k := k) (o := o) h1).mpr hxn⟩

/-- **T2-FIELD, per `i`** (`callField_at`, T2COVER rev2 §1): the served child result `r` of callee `c` ships
(`ShipsRes`, the CHILDREN's IH), `P c = some q`, the design `dsn` contains `r`'s modules, and the field row holds on
`r.1`. Then, at THIS `i` (the `ChildShips` instance), `CallField` has its witnesses. The conclusion does not mention
`i`; the proof instantiates `ChildShips` at `i`. No `Nonempty ι`; no `T1Hyp.dec`. -/
theorem callField_at {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (c : Lean.Name) (r : Tools.ShippingChildInv.Res) (hS : ShipsRes L P c r) (hq : P c = some q)
    (dsn : Sparkle.IR.AST.Design)
    (hDc : ∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g)
    (hmc : Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1)
    (hrow : FieldRowAt p k r.1) (i : ι) :
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o := by
  obtain ⟨-, ⟨q0, n, hq0, -, hCS⟩, -⟩ := hS
  rw [hq] at hq0
  obtain rfl : q = q0 := Option.some.inj hq0
  exact callField_of_outputs p q k r.1 (childRunN_outputs (hCS.2 dsn hDc hmc i)) hrow

/-! ## T2-TIE (CONDITIONAL on DG-SEM / DG-GENP / DG-CLOSINGRUN) -/

/-- **CallTie** (T2COVER rev2 §1 E1): call `k` of `p` to callee `q`, with the decoded families: t2 (`LetTie`, by
definition) and t1+t3 (the route-aware `CallOutF`). -/
def CallTie (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  LetTie p q k hk (decA p q k hk) (Tools.ShippingGen2.decB p q k hk) ∧
    CallOutF p q k (decA p q k hk) (Tools.ShippingGen2.decB p q k hk)

/-- **The DG-SEM row at an ordinary call** (hypothesis shape; DGEN rev2 §2.1 `genSem`'s `ext` at `nDecl + k`): for
every output selected by `CallField`, the parent's call-result signal at `p.kD + k` is that output of the callee's
source on the DECODED families, as a `SigAt` signal of the call's binder kind. Supplied by DG-SEM (unbuilt). -/
def GenExtAtCall (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- **The range row at an ordinary call** (hypothesis shape): the selected callee output lies in the range of the
call's binder kind. NOTE: necessary for any `posEnc … = f τ` (a `BitVec w` / Bool cannot encode an out-of-range
value), so the old `T1Hyp.dec` contained it implicitly; DGEN rev2 names NO row for it. It is assigned to DG-SEM here
as `hDG_SEM_range` and flagged for the design review (a callee-output-range / kind-width row). -/
def CallOutRange (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- **T2-TIE, conditional core**: the per-`i` field (T2-FIELD's output), the DG-SEM call row and the range row give
`CallTie`. -/
theorem callTie_of_dgen (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk := by
  refine ⟨letTie_dec p q k hk, ?_⟩
  intro i bools bits
  obtain ⟨k', o, ho, hcf⟩ := hT2_FIELD i
  obtain ⟨f, hf⟩ := Pkg.src_get q i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits)
    k' o ho
  exact ⟨k', o, f, ho, hcf, hf,
    posEnc_callPos p k i bools bits f (hDG_SEM i bools bits k' o f ho hcf hf)
      (hDG_SEM_range i bools bits k' o f ho hcf hf)⟩

/-- **T2-TIE in the E1 shape** (`callTie_of_closingRun`, CONDITIONAL): `hDG_GENP` (the callee's package under the
closed assignment), `hDG_CLOSINGRUN` (from `ClosingRun.shared`: the served result of call `k`'s callee ships, the
design contains it, and the field row holds), `hDG_SEM`, `hDG_SEM_range`. -/
theorem callTie_of_served {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk) :
    CallTie p q k hk := by
  obtain ⟨r, dsn, hS, hDc, hmc, hrow⟩ := hDG_CLOSINGRUN
  exact callTie_of_dgen p q k hk
    (fun i => callField_at L P p q k (p.d.shape.insts[k]'hk).1 r hS hDG_GENP dsn hDc hmc hrow i)
    hDG_SEM hDG_SEM_range

/-- `CallTie` gives the route-aware `HPointG` (T2-DEC (2), ←). -/
theorem hPointG_of_callTie (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]'hk).1 = some q) (hT : CallTie p q k hk) : HPointG P p q k :=
  (hPointG_iff_callOutDec P p q k hk hP).mpr hT.2

/-! ## T2-STEP (CONDITIONAL on T2-TIE, DG-PKGASSIGN, M3 G-DATA-CALL, G-MEMCALLS) -/

/-- `CallTie` + the static call data (G-DATA-CALL, M3) give `CallDec` (both routes; via `callDec_of_hPointG_at`). -/
theorem callDec_of_callTie (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hG_DATA_CALL_len : (p.d.shape.insts[k]'hk).2.1.length = q.ports.length) :
    CallDec p q k :=
  callDec_of_hPointG_at P p q k hk hP hnone (hPointG_of_callTie P p q k hk hP hT) p.ok
    hG_DATA_CALL_co hG_DATA_CALL_slots hG_DATA_CALL_args hG_DATA_CALL_len

/-- **T2-STEP** (T2COVER rev2 §3 step 4): `StepStmt`'s per-call decoding premise, ordinary calls from `CallTie`
(no `T1Hyp.dec`), memory calls from `MemDec` (unchanged, G-MEMCALLS). CONDITIONAL on every named hypothesis. -/
theorem stepDec_of_ties (P : Pkgs ι dom) (p : Pkg ι dom)
    (hDG_PKGASSIGN : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∃ q, P (p.d.shape.insts[k]).1 = some q)
    (hT2_TIE : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q → CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q →
        callArgsOkAt p.d p.kD k q.portWidths = true ∧ (p.d.shape.insts[k]).2.1.length = q.ports.length)
    (hG_MEMCALLS : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? ≠ none →
      MemDec p k (p.d.shape.insts[k]).1) :
    ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k := by
  intro k hk
  by_cases hnone : (p.d.shape.instOrigins.getD k .ord).child? = none
  · right
    obtain ⟨q, hq⟩ := hDG_PKGASSIGN k hk hnone
    obtain ⟨ha, hl⟩ := hG_DATA_CALL_args k hk hnone q hq
    exact ⟨q, hq, callDec_of_callTie P p q k hk hq hnone (hT2_TIE k hk hnone q hq)
      hG_DATA_CALL_co hG_DATA_CALL_slots ha hl⟩
  · left
    exact hG_MEMCALLS k hk hnone

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.posEnc_of_sigAt
#print axioms Tools.ShippingGen2.sigAt_extendBits_self
#print axioms Tools.ShippingGen2.sigAt_extendBools_self
#print axioms Tools.ShippingGen2.sigAt_extendBits_ne
#print axioms Tools.ShippingGen2.sigAt_extendBools_ne
#print axioms Tools.ShippingGen2.posEnc_callPos
#print axioms Tools.ShippingGen2.childRunN_outputs
#print axioms Tools.ShippingGen2.fieldRow_one_of_callStmt
#print axioms Tools.ShippingGen2.callField_of_outputs
#print axioms Tools.ShippingGen2.callField_at
#print axioms Tools.ShippingGen2.callTie_of_dgen
#print axioms Tools.ShippingGen2.callTie_of_served
#print axioms Tools.ShippingGen2.hPointG_of_callTie
#print axioms Tools.ShippingGen2.callDec_of_callTie
#print axioms Tools.ShippingGen2.stepDec_of_ties
