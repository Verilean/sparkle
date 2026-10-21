import Tools.ShippingLetsReaderInv

/-! # Unit LC3 (pure facts): the total pattern extractors do not invent `_machLet` placeholders

BUILT: UNBUILT (written, first build pending). No `sorry`, no axiom, no `native_decide`.

Discharges, by unfolding, the fields of `PureFacts` (`Tools/ShippingLetsReaderInvBase.lean`) that concern
TOTAL functions: `machLetTail`, `machLoopRegs`, `loopView?`, `machRunApp?`, `machInstCall?`,
`machInstCallS?`, `memCall?`, `machProjIota`. -/
namespace Tools.ShippingLetsReaderInv
open Lean Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel

theorem letTail_ok (n : Nat) : ∀ e : Lean.Expr, LetOk n e = true → LetOk n (machLetTail e) = true := by
  intro e
  induction e with
  | letE nm t v b nd iht ihv ihb =>
    intro he
    simp only [LetOk, Bool.and_eq_true] at he
    simpa only [machLetTail] using ihb he.2
  | _ =>
    intro he
    simpa [machLetTail] using he

theorem loopReg_ok (n : Nat) (a : Lean.Expr) (r : Lean.Expr × Lean.Expr × Lean.Expr)
    (ha : LetOk n a = true) (h : machLoopReg? a = some r) : LetOk n r.2.2 = true := by
  unfold machLoopReg? at h
  split at h
  · injection h with h
    subst h
    simp only [LetOk, Bool.and_eq_true] at ha
    exact ha.2
  · cases h

theorem loopRegs_ok (n : Nat) : ∀ (e : Lean.Expr) (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)),
    LetOk n e = true → machLoopRegs e = some regs → ∀ r ∈ regs, LetOk n r.2.2 = true := by
  intro e
  induction e with
  | app f b ihf ihb =>
    intro regs he h
    unfold machLoopRegs at h
    split at h
    · rename_i heq
      injection heq with hf hb
      subst hf
      subst hb
      simp only [LetOk, Bool.and_eq_true] at he
      try simp only [Option.bind_eq_bind] at h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
      injection h with h
      subst h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact loopReg_ok n _ _ (by okh) hr
      · exact ihb rs (by okh) hrs q hq
    · obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
      subst h
      intro q hq
      rw [List.mem_singleton.mp hq]
      exact loopReg_ok n _ _ he hr
  | _ =>
    intro regs he h
    simp only [machLoopRegs] at h
    obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
    subst h
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact loopReg_ok n _ _ he hr

theorem loopView_ok (n : Nat) (e dom body : Lean.Expr) (he : LetOk n e = true)
    (h : loopView? e = some (dom, body)) : LetOk n dom = true ∧ LetOk n body = true := by
  have hs := ok_spine n e [] he (by simp)
  unfold loopView? at h
  generalize inlSpine e [] = sp at h hs
  obtain ⟨fn, args⟩ := sp
  obtain ⟨hfn, hargs⟩ := hs
  split at h
  · injection h with h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp_all [LetOk]
  · cases h

theorem runApp_ok (n : Nat) (e dom αs inits body : Lean.Expr) (he : LetOk n e = true)
    (h : machRunApp? e = some (dom, αs, inits, body)) : LetOk n dom = true ∧ LetOk n body = true := by
  have hs := ok_spine n e [] he (by simp)
  unfold machRunApp? at h
  generalize inlSpine e [] = sp at h hs
  obtain ⟨fn, args⟩ := sp
  obtain ⟨hfn, hargs⟩ := hs
  split at h
  · injection h with h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp_all [LetOk]
  · cases h

theorem instCall_ok (senv : StructEnv) (n : Nat) (e : Lean.Expr) (c : Name)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (he : LetOk n e = true) (h : machInstCall? senv e = some (c, kinds, res, args)) :
    ∀ a ∈ args, LetOk n a = true := by
  have hs := ok_spine n e [] he (by simp)
  unfold machInstCall? at h
  split at h
  · rename_i heq0
    rw [heq0] at hs
    dsimp only at hs
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        exact hs.2
      · cases h
    · cases h
  · cases h

theorem instCallS_ok (senv : StructEnv) (n : Nat) (e : Lean.Expr) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (he : LetOk n e = true) (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    ∀ a ∈ args, LetOk n a = true := by
  have hs := ok_spine n e [] he (by simp)
  unfold machInstCallS? at h
  split at h
  · rename_i heq0
    rw [heq0] at hs
    dsimp only at hs
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        exact hs.2
      · cases h
    · cases h
  · cases h

theorem memCall_ok (natOf : Lean.Expr → Option Nat) (n : Nat) (e : Lean.Expr) (combo : Bool)
    (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr) (he : LetOk n e = true)
    (h : Sparkle.Compiler.MachMemory.memCall? natOf e = some (combo, aw, dw, dom, ops)) :
    LetOk n dom = true ∧ ∀ o ∈ ops, LetOk n o = true := by
  have hargs := ok_getAppArgs he
  unfold Sparkle.Compiler.MachMemory.memCall? at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl, rfl⟩ := h
        refine ⟨ok_getElem! hargs 0, ?_⟩
        intro o ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl <;> exact ok_getElem! hargs _
    · cases h

theorem getD_ok {n : Nat} {e : Lean.Expr} {o : Option Lean.Expr} (he : LetOk n e = true)
    (ho : ∀ x, o = some x → LetOk n x = true) : LetOk n (o.getD e) = true := by
  cases o with
  | none => exact he
  | some x => exact ho x rfl

theorem projIota_ok (projs : Name → Option (Name × Nat × Nat)) (n : Nat) (e : Lean.Expr)
    (he : LetOk n e = true) : LetOk n (machProjIota projs e) = true := by
  have hs := ok_spine n e [] he (by simp)
  unfold machProjIota
  split
  · rename_i heq0
    rw [heq0] at hs
    dsimp only at hs
    split
    · rename_i r _ hq
      split
      · have hrm := List.mem_of_getLast? hq
        have hrok : LetOk n r = true := hs.2 r hrm
        have hs2 := ok_spine n r [] hrok (by simp)
        split
        · rename_i heq2
          rw [heq2] at hs2
          dsimp only at hs2
          split
          · exact getD_ok he (fun x hx => hs2.2 x (List.mem_of_getElem? hx))
          · exact he
        · exact he
      · exact he
    · exact he
  · exact he

end Tools.ShippingLetsReaderInv
