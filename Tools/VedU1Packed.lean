import Tools.VedU1Contract

/-!
# U1 contract for a packed result `Signal d (A × B)` (docs/VED-U1-PACKED.md)

The synthesizer packs a product result into ONE port `out` of width `Σ wᵢ`: the
leaves left-first, the FIRST leaf in the HIGH bits (Sparkle/Compiler/Elab.lean:374,
1399-1406; MSB-first `concat`, Sparkle/IR/Semantics.lean:142-156).  This file
states what a returned module must satisfy for such a declaration, next to
(not instead of) the separate-port `U1Stmt`.
-/

namespace Tools.VedU1Packed

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

/-! ## The packing map of a result tree -/

/-- Pointwise relation of two lists of equal length. -/
def All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ All2 R as bs
  | _, _ => False

theorem all2_append {α β : Type} {R : α → β → Prop} : ∀ {l1 l2 : List α} {m1 m2 : List β},
    All2 R l1 m1 → All2 R l2 m2 → All2 R (l1 ++ l2) (m1 ++ m2)
  | [], l2, [], m2, _, h2 => h2
  | a :: as, l2, b :: bs, m2, ⟨h, hs⟩, h2 => ⟨h, all2_append hs h2⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem all2_map_left {α α' β : Type} {R : α' → β → Prop} (g : α → α') :
    ∀ {l : List α} {m : List β}, All2 R (l.map g) m → All2 (fun a b => R (g a) b) l m
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨h, hs⟩ => ⟨h, all2_map_left g hs⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem all2_map_left' {α α' β : Type} {R : α' → β → Prop} (g : α → α') :
    ∀ {l : List α} {m : List β}, All2 (fun a b => R (g a) b) l m → All2 R (l.map g) m
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨h, hs⟩ => ⟨h, all2_map_left' g hs⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem all2_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {m : List β}, All2 R l m → All2 S l m
  | [], [], _ => trivial
  | a :: as, b :: bs, ⟨h1, hs⟩ => ⟨h a b h1, all2_imp h hs⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim


/-- Total width of a tree: the sum of its leaves. -/
def _root_.Tools.VedU1Contract.OTy.width : OTy → Nat
  | .leaf p => p.width
  | .pair a b => a.width + b.width

/-- `(offset, width)` of every leaf, left-first, relative to the packed tree: the first
leaf is in the HIGH bits, so the left side is shifted up by the right side's width. -/
def _root_.Tools.VedU1Contract.OTy.slices : OTy → List (Nat × Nat)
  | .leaf p => [(0, p.width)]
  | .pair a b => a.slices.map (fun s => (s.1 + b.width, s.2)) ++ b.slices

/-- The packed value of a leaf. -/
def _root_.Tools.VedU1Contract.PTy.pack : (p : PTy) → p.val → BitVec p.width
  | .bit, b => BitVec.ofBool (show Bool from b)
  | .bv _, v => v

/-- The packed value of a tree: `BitVec.append`, the left part high. -/
def _root_.Tools.VedU1Contract.OTy.pack : (o : OTy) → o.val → BitVec o.width
  | .leaf p, v => p.pack v
  | .pair a b, v => a.pack v.1 ++ b.pack v.2

theorem _root_.Tools.VedU1Contract.OTy.length_slices (o : OTy) : o.slices.length = o.flat.length := by
  induction o with
  | leaf p => rfl
  | pair a b iha ihb => simp [OTy.slices, OTy.flat, iha, ihb]

/-! ## Slices of a packed value are the leaves' observations -/

/-- The slice `(offset, width)` of a packed number. -/
def sliceOf (x : Nat) (s : Nat × Nat) : Nat := (x >>> s.1) % 2 ^ s.2

theorem sliceOf_high (pa pb wb o w : Nat) (hb : pb < 2 ^ wb) :
    sliceOf (pa <<< wb ||| pb) (o + wb, w) = sliceOf pa (o, w) := by
  unfold sliceOf
  have h : (pa <<< wb ||| pb) >>> (o + wb) = pa >>> o := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
    have : pb.testBit (o + wb + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))
    have e : o + wb + i - wb = o + i := by omega
    simp [this, e, show wb ≤ o + wb + i by omega]
  simp only [h]

theorem sliceOf_low (pa pb wb o w : Nat) (hbd : o + w ≤ wb) :
    sliceOf (pa <<< wb ||| pb) (o, w) = sliceOf pb (o, w) := by
  unfold sliceOf
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < w
  · have : ¬ (wb ≤ o + i) := by omega
    simp [this]
  · simp [hi]

theorem _root_.Tools.VedU1Contract.OTy.slices_obs (o : OTy) (v : o.val) :
    All2 (fun s w => s.1 + s.2 ≤ o.width ∧ sliceOf (o.pack v).toNat s = w)
      o.slices (o.obs v) := by
  induction o with
  | leaf p =>
    simp only [OTy.slices, OTy.obs, OTy.pack, OTy.width]
    refine ⟨⟨by simp, ?_⟩, trivial⟩
    have hlt := (p.pack v).isLt
    unfold sliceOf
    cases p with
    | bit => simp [PTy.pack, PTy.obs, PTy.width] at hlt ⊢; exact hlt
    | bv w => simp [PTy.pack, PTy.obs, PTy.width, Nat.mod_eq_of_lt (BitVec.isLt v)]
  | pair a b iha ihb =>
    simp only [OTy.slices, OTy.obs, OTy.pack, OTy.width, BitVec.toNat_append]
    have ha := iha v.1
    have hb := ihb v.2
    have hlt := (b.pack v.2).isLt
    apply all2_append
    · apply all2_map_left'
      refine all2_imp ?_ ha
      intro s w ⟨h1, h2⟩
      refine ⟨by simp; omega, ?_⟩
      rw [sliceOf_high _ _ _ _ _ hlt]; exact h2
    · refine all2_imp ?_ hb
      intro s w ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      rw [sliceOf_low _ _ _ _ _ h1]; exact h2

/-- The packed value as a number (the same value as `(o.pack v).toNat`, without the width-dependent type):
leaf `i` is `obs_i` shifted by the widths of the leaves after it. -/
def _root_.Tools.VedU1Contract.OTy.packNat : (o : OTy) → o.val → Nat
  | .leaf p, v => p.obs v
  | .pair a b, v => a.packNat v.1 <<< b.width ||| b.packNat v.2

theorem OTy.toNat_pack (o : OTy) (v : o.val) : (o.pack v).toNat = o.packNat v := by
  induction o with
  | leaf p =>
    cases p with
    | bit => cases v <;> rfl
    | bv w => rfl
  | pair a b iha ihb =>
    show (a.pack v.1 ++ b.pack v.2).toNat = a.packNat v.1 <<< b.width ||| b.packNat v.2
    rw [BitVec.toNat_append, iha, ihb]

/-- A low field that fits its width: shift-or is shift-add. -/
theorem cat_eq (a b w : Nat) (hb : b < 2 ^ w) : a <<< w ||| b = a * 2 ^ w + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

/-- A one-bit port read back from its stream value. -/
theorem bne_toNat (x : Nat) (h : x < 2) : (x != 0).toNat = x := by
  rcases Nat.lt_or_ge x 1 with h0 | h1
  · have : x = 0 := by omega
    subst this; rfl
  · have : x = 1 := by omega
    subst this; rfl

/-- Bounds of bitwise combinations of numbers below a power of two (the side conditions the
generated scripts discharge with `ltb`; the literal `n` is checked to be a power of two by `decide`). -/
theorem or_lt_lit (a b n : Nat) (ha : a < n) (hb : b < n) (hn : n = 2 ^ Nat.log2 n) : a ||| b < n := by
  rw [hn] at ha hb ⊢; exact Nat.or_lt_two_pow ha hb

theorem xor_lt_lit (a b n : Nat) (ha : a < n) (hb : b < n) (hn : n = 2 ^ Nat.log2 n) : a ^^^ b < n := by
  rw [hn] at ha hb ⊢; exact Nat.xor_lt_two_pow ha hb

theorem and_lt_left (a b n : Nat) (ha : a < n) : a &&& b < n :=
  Nat.lt_of_le_of_lt Nat.and_le_left ha

theorem and_lt_right (a b n : Nat) (hb : b < n) : a &&& b < n :=
  Nat.lt_of_le_of_lt Nat.and_le_right hb

theorem shl_lt_div (x w n : Nat) (hx : x < n / 2 ^ w) : x <<< w < n := by
  rw [Nat.shiftLeft_eq]
  have h1 : (x + 1) * 2 ^ w ≤ n / 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ hx
  have h2 := Nat.div_mul_le_self n (2 ^ w)
  rw [Nat.add_mul, Nat.one_mul] at h1
  have := Nat.two_pow_pos w
  omega

/-- Discharger for the bound side conditions of the generated scripts. -/
syntax "ltb" : tactic

macro_rules
  | `(tactic| ltb) =>
    `(tactic| first
    | omega
    | (refine or_lt_lit _ _ _ ?_ ?_ (by decide) <;> ltb)
    | (refine xor_lt_lit _ _ _ ?_ ?_ (by decide) <;> ltb)
    | (refine and_lt_left _ _ _ ?_; ltb)
    | (refine and_lt_right _ _ _ ?_; ltb)
    | (refine shl_lt_div _ _ _ ?_; ltb))

/-! ## The coverage check -/

/-- A slice map covers a port of width `W` for leaves of the given widths:
one slice per leaf with the leaf's width, offsets DESCENDING (leaf 0 highest), each slice inside
the port, slices pairwise disjoint, and the widths add up to `W` (every port bit lies in a slice). -/
def SliceCover (ws : List Nat) (W : Nat) (ss : List (Nat × Nat)) : Prop :=
  ss.map Prod.snd = ws ∧
  ss.Pairwise (fun a b => b.1 + b.2 ≤ a.1) ∧
  (∀ s ∈ ss, s.1 + s.2 ≤ W) ∧
  ws.sum = W ∧
  (ss.map fun s => (List.range s.2).map (· + s.1)).flatten.Nodup ∧
  (∀ k, k < W → ∃ s ∈ ss, s.1 ≤ k ∧ k < s.1 + s.2)

instance (ws W ss) : Decidable (SliceCover ws W ss) := by
  unfold SliceCover; infer_instance

/-! ## Contract -/

/-- The table of the collapsed (single packed port) view. -/
def collapse (tbl : DeclTable) : DeclTable :=
  { tbl with out := .leaf (.bv (OTy.width tbl.out)) }

/-- Fixed by the entry: the declaration's table (its `Prod` tree), the packed port and its
slice map, and the module fields the meaning reads (register-free scope). -/
structure PContract where
  modName : String
  tbl     : DeclTable
  port    : String
  slices  : List (Nat × Nat)
  inNames : List String
  wires   : List Port
  deriving Repr, DecidableEq

/-- The ordinary contract of the packed port (one `bv W` output). -/
def PContract.core (pc : PContract) : Contract :=
  { modName := pc.modName, clkRst := none, table := collapse pc.tbl,
    inNames := pc.inNames, outNames := [pc.port], wires := pc.wires, inits := [] }

/-- `InTy` with a mapped result. -/
def InTy.mapOut {R S : Type} (g : R → S) : (ps : List PTy) → InTy ps R → InTy ps S
  | [], f => g f
  | _ :: ps, f => fun x => InTy.mapOut g ps (f x)

/-- The declaration with its result packed (`BitVec.append`, left high). -/
def packedF (tbl : DeclTable) (f : tbl.Ty) : (collapse tbl).Ty :=
  InTy.mapOut (fun s => Signal.map (OTy.pack tbl.out) s) tbl.ins f

/-- Slice map is the packing rule's, and covers the port. -/
def PackCover (pc : PContract) : Prop :=
  pc.slices = pc.tbl.out.slices ∧
  SliceCover (pc.tbl.out.flat.map PTy.width) pc.tbl.out.width pc.slices ∧
  0 < pc.tbl.out.flat.length ∧ pc.tbl.out.flat.length ≥ 2

instance (pc : PContract) : Decidable (PackCover pc) := by
  unfold PackCover; infer_instance

/-- On every run, the packed port is in range and every slice equals the declaration's own
projection (observation of the original declaration's result, left-first). -/
def SlicesOn (pc : PContract) (m : Module) (b : List Stmt) (f : pc.tbl.Ty) : Prop :=
  ∀ ins, InputsOk pc.core m ins → ∀ K, ∃ envs,
    runModule (declWidth m) b (seedFwd m K ins) K (st0 pc.core m) (fun _ _ => 0) = some envs ∧
    ∀ t, t < K → ∃ env, envs[t]? = some env ∧
      env pc.port < 2 ^ pc.tbl.out.width ∧
      All2 (fun s v => sliceOf (env pc.port) s = v) pc.slices
        (pc.tbl.out.obs ((applyIns pc.tbl.ins pc.inNames ins f).val t))

def SlicesStmt (pc : PContract) (m : Module) (f : pc.tbl.Ty) : Prop :=
  ∀ b, b.Perm m.body → Sparkle.IR.Reorder.WO [] b → SlicesOn pc m b f


/-! ## The packed statement follows from the ordinary one -/

theorem applyIns_mapOut {R S : Type} (g : R → S) (ps : List PTy) (ns : List String)
    (ins : Nat → String → Nat) (f : InTy ps R) :
    applyIns ps ns ins (InTy.mapOut g ps f) = g (applyIns ps ns ins f) := by
  induction ps generalizing ns with
  | nil => rfl
  | cons p ps ih => exact ih _ _

theorem srcOf_packed (pc : PContract) (f : pc.tbl.Ty) (ins : Nat → String → Nat) (t : Nat) :
    srcOf pc.core (packedF pc.tbl f) ins pc.port t =
      pc.tbl.out.packNat ((applyIns pc.tbl.ins pc.inNames ins f).val t) := by
  have e : applyIns pc.tbl.ins pc.inNames ins
      (InTy.mapOut (fun s => Signal.map pc.tbl.out.pack s) pc.tbl.ins f) =
      Signal.map pc.tbl.out.pack (applyIns pc.tbl.ins pc.inNames ins f) := applyIns_mapOut _ _ _ _ _
  simp only [srcOf, PContract.core, collapse, packedF, OTy.obs, PTy.obs,
    List.zip_cons_cons, List.zip_nil_left, List.lookup, beq_self_eq_true, if_true, Option.getD_some]
  erw [e]
  exact OTy.toNat_pack _ _

/-- Outputs of the packed view give the slice statement: every slice of the port is the declaration's
own projection, and the port is in range. -/
theorem slices_of_outputs {pc : PContract} {m : Module} {f : pc.tbl.Ty}
    (hc : pc.slices = pc.tbl.out.slices)
    (h : OutputsStmt pc.core m (packedF pc.tbl f)) : SlicesStmt pc m f := by
  intro b hb hwo ins hok K
  obtain ⟨envs, hrun, hall⟩ := h b hb hwo ins hok K
  refine ⟨envs, hrun, fun t ht => ?_⟩
  obtain ⟨env, he, hv⟩ := hall t ht ⟨pc.port, .bitVector pc.tbl.out.width⟩ (List.mem_cons_self ..)
  refine ⟨env, he, ?_⟩
  have hv' : env pc.port = (pc.tbl.out.pack ((applyIns pc.tbl.ins pc.inNames ins f).val t)).toNat := by
    rw [hv, srcOf_packed, OTy.toNat_pack]
  rw [hv', hc]
  refine ⟨BitVec.isLt _, ?_⟩
  exact all2_imp (fun s v hh => hh.2) (OTy.slices_obs pc.tbl.out ((applyIns pc.tbl.ins pc.inNames ins f).val t))

/-- The statement the packed entry registers. -/
def PackedStmt (pc : PContract) (m : Module) (f : pc.tbl.Ty) : Prop :=
  PackCover pc ∧ U1Stmt pc.core m (packedF pc.tbl f) ∧ SlicesStmt pc m f

end Tools.VedU1Packed
