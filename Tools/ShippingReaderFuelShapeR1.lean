import Tools.ShippingReaderFuelR1
import Tools.ShippingReaderFuelShapeR5
import Tools.ShippingCallWidthsEntry

/-! # Wrapper-level R1 for the fuel CANDIDATE `machineShapeF`

BUILT: run `k1` (poc a6573291) FAILED (exit 1: a multi-line `first`
alternative at 104 did not parse, unsolved goal at 95 as its consequence;
`rw [he] at hc ⊢` at 163 failed); integrator fixes (one alternative per line;
`try rw [he] at hc` / `try rw [he]`), statements unchanged; run `k2` exit 0 (worker K, branch `par/r-15`, from poc
`20304f50`; reviewer 2026-10-17 item 2(b)). No `sorry`, no axiom, no
`native_decide`. No compiler change.

SCOPE. Statements about the fuel candidate wrapper `machineShapeF` only; NOT
about the old `machineShape?` (O1/O2 not done).

The phases of `machineShapeF_steps` (`Tools/ShippingReaderFuelShapeR5.lean`)
keep `InstR1` (`Tools/ShippingReaderFuelR1.lean`): the initial state `{}` has
no entries, `machReserve` does not write `insts`, the root-let fold, the body
and the readers keep it (`readF_good1`), and `shapePost` copies `st.insts`
into the shape (`shapePost_insts`).

* `machineShapeF_instR1` — every call entry `(c, js, r)` of a successful
  candidate result has `r = r'` whenever `senv.inst c = some (_, r')`, under
  `MemR1 senv` and `SigDisj senv`;
* `machineShapeF_r1At` — `R1At env sp k` (the predicate of
  `Tools/ShippingCallWidthsEntry.lean`) for every `k`, for a shape read with
  `structEnv env`, under `MemR1 (structEnv env)` only (`SigDisj` is proved);
* `machineShapeF_r1k` — the consumer's `R1k` for entry `k` whose callee `c`
  has signature `(kinds, res)` in `env`.

MEASURED axioms (run `ax18`, poc after 3a1938a3): `machineShapeF_r1k`:
[propext, Classical.choice, Quot.sound]. -/
namespace Tools.ShippingReaderFuelShapeR1
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel
open Tools.ShippingReaderLenOk
open Tools.ShippingMachineShapeUnfold
open Tools.ShippingShapeDecomp
open Tools.ShippingReaderFuelShapeR5
open Tools.ShippingReaderFuelR1

/-! ## The shape's call entries are the final state's -/

/-- `shapePost` (5132–5185) copies the final state's `insts` into the shape
(same unfolding as `shapePost_decomp`). -/
theorem shapePost_insts {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    sp.insts = st.insts.toList := by
  unfold shapePost at h
  try dsimp only at h
  repeat' first
    | (replace h := ite_none_inv h)
    | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
    | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
    | (split at h)
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    try (replace h := ite_else_none_inv h)
    have hsp := Option.some.inj h
    subst hsp
    rfl

/-! ## The phases keep `InstR1` -/

section Phases
variable {senv : StructEnv} {n : Nat}

theorem shapeStart_instR1 {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) : InstR1 senv st0 := by
  rcases shapeStart_inv hr with ⟨_, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, hres⟩
  · rw [h0]
    exact instR1_init
  · exact machReserve_instR1 instR1_init hres

theorem shapeRootLet_instR1 (hM : MemR1 senv) (hD : SigDisj senv) :
    ∀ (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
      (s' : List MachVal × MachRead),
      InstR1 senv s.2 → (shapeRootLet senv s a).run (wtab senv n) = some (some s') →
        InstR1 senv s'.2 := by
  rintro ⟨env, st⟩ ⟨nm, ty, v⟩ s' hst hr
  have hst' : InstR1 senv st := hst
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · -- a `Signal.loop` root
    obtain ⟨⟨mv, st2⟩, hl, hr⟩ := bindO_some_inv hr
    have h2 : InstR1 senv st2 :=
      readF_good1 senv hM hD n (Call.loopRoot env v st) True.intro hst' (mv, st2) hl
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact h2
  · split at hr
    · -- an ordinary root `let`
      obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have h2 : InstR1 senv st2 :=
        readF_good1 senv hM hD n (Call.conv env 0 v st) True.intro hst' (v', st2) hc
      try dsimp only at hr
      revert hr
      first
        | (intro hr; have e := okO_run_inv hr; subst e; exact instR1_congr h2 (by rfl))
        | (split <;> (intro hr; have e := okO_run_inv hr; subst e; exact instR1_congr h2 (by rfl)))
        | ((repeat' split) <;> (intro hr; have e := okO_run_inv hr; subst e; exact instR1_congr h2 (by rfl)))
    · exact (failO_run_inv hr).elim

theorem rootLets_instR1 (hM : MemR1 senv) (hD : SigDisj senv)
    {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal} {st0 st1 : MachRead}
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1)))
    (h0 : InstR1 senv st0) : InstR1 senv st1 :=
  foldO_inv (fun s : List MachVal × MachRead => InstR1 senv s.2)
    (shapeRootLet_instR1 (senv := senv) (n := n) hM hD) l (env, st0) (env', st1) h0 hr

theorem shapeBody_instR1 (hM : MemR1 senv) (hD : SigDisj senv) {m : ShapeMid}
    {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (h1 : InstR1 senv st1) : InstR1 senv st := by
  rcases shapeBody_inv hr with ⟨_, _, _, _, ws, v0, st2, _, hc, hst⟩ | ⟨_, hc⟩
  · rw [hst]
    exact instR1_congr (machChainF_instR1 hM hD hc h1) (by rfl)
  · exact machConvF_instR1 hM hD hc h1

end Phases

/-! ## The whole wrapper -/

section Wrapper
variable {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
  {senv : StructEnv} {ai : Bool} {sp : MachineShape}

/-- **R1 of every successful candidate result** (every call entry). -/
theorem machineShapeF_instR1 (hM : MemR1 senv) (hD : SigDisj senv)
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∀ (c : Name) (js : List Nat) (r : MixedGateBinder), (c, js, r) ∈ sp.insts →
      ∀ (kinds : List MixedGateBinder) (r' : MixedGateBinder),
        senv.inst c = some (kinds, r') → r = r' := by
  obtain ⟨p, en, st0, env, st1, st, v, _, _, h0, h1, h2, h3⟩ := machineShapeF_steps h
  have l0 : InstR1 senv st0 := shapeStart_instR1 h0
  have l1 : InstR1 senv st1 := rootLets_instR1 hM hD h1 l0
  have l2 : InstR1 senv st := shapeBody_instR1 hM hD h2 l1
  rw [shapePost_insts h3]
  exact l2

/-- R1 at entry `k`, for any signature table (the `R1At` statement with
`senv` in place of `structEnv env`). -/
theorem machineShapeF_r1k (hM : MemR1 senv) (hD : SigDisj senv)
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) {k : Nat} {c : Name}
    {kinds : List MixedGateBinder} {res : MixedGateBinder}
    (hc : (sp.insts.map (·.1))[k]? = some c) (hi : senv.inst c = some (kinds, res)) :
    (sp.insts.map (·.2.2))[k]? = some res := by
  rw [List.getElem?_map] at hc ⊢
  cases he : sp.insts[k]? with
  | none =>
    rw [he] at hc
    first
      | cases hc
      | (simp at hc)
  | some x =>
    obtain ⟨c0, js, r⟩ := x
    try rw [he] at hc
    try rw [he]
    have hc' : c0 = c := Option.some.inj hc
    subst hc'
    have e := machineShapeF_instR1 hM hD h c0 js r (List.mem_of_getElem? he) kinds res hi
    subst e
    rfl

/-- **`R1At` for a candidate-read shape** (`Tools/ShippingCallWidthsEntry.lean`'s
predicate), for the real signature table `structEnv env`: only `MemR1` is
assumed (`SigDisj` is `sigDisj_structEnv`). -/
theorem machineShapeF_r1At {env : Environment} (hM : MemR1 (structEnv env))
    (h : machineShapeF n sm ps ci (structEnv env) ai = some (some sp)) (k : Nat) :
    Tools.ShippingCallWidthsEntry.R1At env sp k := by
  intro c kinds res hc hi
  exact machineShapeF_r1k hM (sigDisj_structEnv env) h hc hi

end Wrapper

end Tools.ShippingReaderFuelShapeR1
