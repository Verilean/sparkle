import Tools.VedU1TableGen

/-!
# Named constant-table leaves (issue sparkle-ved-hier3-child)

`Tools/VedU1TableGen.lean` proves a `kLut!` table whose body has the textbook skeleton (`4t + 2`
statements named `Wt t p`, indices `0 … t-1`).  A hand-written mux chain (`Signal.mux (eqK cnt k) bₖ …`
over `let`-bound constants, as `httpRespByte`) or a table whose constants the compiler shares has other
names, another statement count and other index constants.  What these bodies have in common is only
that they are straight-line `const` / `alias` / `eq` against the one input / `mux` statements.

`NData` is such a body as data: the wire name of each position and its form.  The kernel checks that the
synthesized body IS `NData.body` and one Bool (`NData.ok`: every form reads earlier positions, the names
are distinct, none is the input, the last one is `out`); `step_ntbl` evaluates the body once, by the
induction `eval_bodyN` of the table route, to the value of the output position.  The value itself is a
computation on the form list (`NData.out x`) that the kernel decides for every input value
(`NData.out_eq`), so no shape of the chain (index offset, order, repeated or missing entries) is built
into the proof.

Untrusted like the script: the kernel checks everything.
-/

namespace Tools.VedH3ChildTbl

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder Tools.VedU1Contract Tools.VedU1Table Tools.VedU1TableGen

/-- a name as a number: only used to check that names are distinct without comparing strings (the
kernel compares string literals slowly); a collision can only make the check fail -/
def enc (s : String) : Nat := s.toList.foldl (fun a c => a * 1114113 + c.toNat + 1) 0

structure NData where
  ns : List String
  Fl : List Form
  inp : String
  iw : Nat
  w : Nat
  /-- `enc` of the names (precomputed: the kernel would evaluate `enc` at every comparison) -/
  nse : List Nat
  /-- the field width of a packed row -/
  fw : Nat
  /-- `rows[x]`: the value of every position at the input value `x`, packed `fw` bits each (computed by
  the untrusted reader, checked by `rowsOk`) -/
  rows : List Nat

/-- field `p` of a packed row -/
def rowGet (fw r p : Nat) : Nat := (r >>> (fw * p)) % 2 ^ fw

def NData.N (D : NData) : Nat := D.Fl.length
def NData.Fn (D : NData) : Nat → Form := fun p => D.Fl.getD p (.const 0 0)
def NData.W (D : NData) : Nat → String := fun p => D.ns.getD p ""
def NData.body (D : NData) : List Stmt := bodyN D.inp D.W D.Fn 0 D.N

def NData.ok (D : NData) : Bool :=
  decide (1 ≤ D.N) && (D.ns.length == D.N) &&
  (List.range D.N).all (fun p => (D.Fn p).reads.all (fun j => decide (j < p))) &&
  (D.ns.map enc == D.nse) && decide D.nse.Nodup && decide (enc D.inp ∉ D.nse) && (D.ns.getD (D.N - 1) "" == "out")

/-- the rows are consistent: every position equals its form evaluated on the row -/
def NData.rowsOk (D : NData) : Bool :=
  (D.rows.length == 2 ^ D.iw) &&
  (List.range (2 ^ D.iw)).all (fun x =>
    let r := D.rows.getD x 0
    (List.range D.N).all (fun p => rowGet D.fw r p == (D.Fn p).ev x (fun j => rowGet D.fw r j)))

/-- the value of the output position (the last one) at the input value `x` -/
def NData.out (D : NData) (x : Nat) : Nat := rowGet D.fw (D.rows.getD x 0) (D.N - 1)

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  unfold List.Nodup at h ⊢
  rw [List.pairwise_map] at h
  exact h.imp (fun {a b} (hab : f a ≠ f b) (e : a = b) => hab (congrArg f e))

theorem NData.ok_sound (D : NData) (h : D.ok = true) :
    1 ≤ D.N ∧ D.ns.length = D.N ∧ ValidN D.Fn D.N ∧ D.ns.Nodup ∧ D.inp ∉ D.ns ∧
    D.W (D.N - 1) = "out" := by
  simp only [NData.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4a⟩, h4b⟩, h5⟩, h6⟩ := h
  have hnd : D.ns.Nodup := nodup_of_map enc (h4a ▸ h4b)
  refine ⟨h1, h2, fun p hp j hj => h3 p hp j hj, hnd, ?_, h6⟩
  intro hm
  exact h5 (h4a ▸ List.mem_map_of_mem hm)

/-- a row that satisfies every form is the value function -/
theorem row_V (Fn : Nat → Form) (N x : Nat) (hv : ValidN Fn N) (row : Nat → Nat)
    (h : ∀ p, p < N → row p = (Fn p).ev x row) :
    ∀ p, p < N → row p = V x Fn p := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro hp
    rw [h p hp, V_eq x Fn p (hv p hp)]
    apply Form.ev_congr
    intro j hj
    exact ih j (hv p hp j hj) (by have := hv p hp j hj; omega)

theorem NData.out_eq (D : NData) (hok : D.ok = true) (hr : D.rowsOk = true) (x : Nat) (hx : x < 2 ^ D.iw) :
    D.out x = V x D.Fn (D.N - 1) := by
  simp only [NData.rowsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at hr
  obtain ⟨_, h2⟩ := hr
  have h3 := h2 x hx
  obtain ⟨hN, _, hv, _⟩ := D.ok_sound hok
  exact row_V D.Fn D.N x hv (rowGet D.fw (D.rows.getD x 0)) (fun p hp => h3 p hp) (D.N - 1) (by omega)

theorem NData.W_inj (D : NData) (h : D.ok = true) :
    ∀ a b, a < D.N → b < D.N → D.W a = D.W b → a = b := by
  obtain ⟨_, hl, _, hnd, _, _⟩ := D.ok_sound h
  intro a b ha hb hab
  simp only [NData.W, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a < D.ns.length by omega),
    List.getElem?_eq_getElem (show b < D.ns.length by omega), Option.getD_some] at hab
  have e : D.ns[a]? = D.ns[b]? := by
    rw [List.getElem?_eq_getElem (show a < D.ns.length by omega),
      List.getElem?_eq_getElem (show b < D.ns.length by omega), hab]
  exact (List.getElem?_inj (show a < D.ns.length by omega) hnd).1 e

theorem NData.W_ne_inp (D : NData) (h : D.ok = true) : ∀ a, a < D.N → D.W a ≠ D.inp := by
  obtain ⟨_, hl, _, _, hi, _⟩ := D.ok_sound h
  intro a ha e
  apply hi
  rw [← e]
  simp only [NData.W, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a < D.ns.length by omega),
    Option.getD_some]
  exact List.getElem_mem _

theorem all_bodyN' (inp : String) (W : Nat → String) (Fn : Nat → Form) :
    ∀ (n i : Nat), (bodyN inp W Fn i n).all isAsg = true := all_bodyN inp W Fn

/-- the wire list of a module whose wires are the input and every position but the last -/
theorem NData.nodup_wires (D : NData) (h : D.ok = true) : (D.inp :: D.ns.dropLast).Nodup := by
  obtain ⟨_, _, _, hnd, hi, _⟩ := D.ok_sound h
  refine List.nodup_cons.2 ⟨fun hm => hi (List.dropLast_subset _ hm), hnd.sublist (List.dropLast_sublist _)⟩

/-- One cycle of a named body: no register update, memories unchanged, `out` the value of the last
position. -/
theorem step_ntbl (D : NData) (hok : D.ok = true) (we : WEnv) (mems : MEnv) (env0 : Env) :
    ∃ envF, stepModule we D.body env0 mems = some (envF, [], mems) ∧
      envF "out" = V (env0 D.inp) D.Fn (D.N - 1) := by
  obtain ⟨hN, hl, hv, hnd, hi, hlast⟩ := D.ok_sound hok
  have hW := D.W_inj hok
  have hI := D.W_ne_inp hok
  obtain ⟨env', hrun, _, hval⟩ := eval_bodyN we mems D.inp D.W D.Fn (env0 D.inp) D.N hv hW hI
    D.N 0 env0 (by omega) rfl (fun j hj => absurd hj (Nat.not_lt_zero _))
  refine ⟨env', ?_, ?_⟩
  · unfold NData.body
    simp only [stepModule, hrun, regNexts_asg we mems _ _ (all_bodyN _ _ _ _ _),
      memNexts_asg we _ mems _ (all_bodyN _ _ _ _ _), Option.bind_eq_bind, Option.bind_some]
  · have := hval (D.N - 1) (by omega)
    rw [hlast] at this
    rw [this]

/-- the body is a well-ordered netlist -/
theorem orderOk_ntbl (D : NData) (hok : D.ok = true) (m : Sparkle.IR.AST.Module)
    (hbody : m.body = D.body) (hin : m.inputs.map (·.name) = [D.inp])
    (hout : ∀ p ∈ m.outputs, p.name = "out") : OrderOk m D.body = true := by
  obtain ⟨hN, hl, hv, hnd, hi, hlast⟩ := D.ok_sound hok
  exact orderOk_bodyN m D.inp D.W D.Fn D.N hv (D.W_inj hok) (D.W_ne_inp hok) hbody hin
    (fun p hp => ⟨D.N - 1, by omega, by rw [hout p hp, hlast]⟩)

end Tools.VedH3ChildTbl
