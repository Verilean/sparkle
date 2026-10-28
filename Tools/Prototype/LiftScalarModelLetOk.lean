import Tools.Prototype.BoolMapModelLetOk

/-! # Unit LC17: a kernel-visible (fuel) model of `machLiftScalarN`; `LiftScalarRange` replaced by ONE correspondence lemma

BUILT (unit LC17): c1-c7 exit 1/0 while developing (my proof errors), c8 exit 0 (`liftStep_ok`), c9 exit 0 (this file, final). Test: Tests/Compiler/LiftScalarModelAgreeTest.lean, t2 exit 0 (t1 exit 1: my grid had too few refusals). No sorry / axiom / native_decide.

MODEL. `machLiftScalarN` is a `partial def`, so the kernel has no equations for it. `liftStep self senv dom vars` is ONE
unfolding of it: the text of every arm of `machLiftScalarN` (var reference `.bvar i => vars[i]?`; the six-argument
binary-operator arm incl. `++`; the closed-constant default `machLiftConst`; and the `BitVec.append` / `extractLsb'` / `not` /
`signExtend` / `sshiftRight` / `Signal.ashr` / `Neg.neg` / `Complement.complement` arms), with every recursive call
`machLiftScalarN senv dom vars ·` replaced by the parameter `self`. `liftN fuel` ties the knot with a fuel (the `ashr` arm
recurses on a REBUILT term, so there is no structural recursion on the input); `liftN 0 = none`.
Callees of the model: TOTAL ones used directly (`machBits?`, `canonicalNatLitValue?`, `bitVecLitValue?`, `machSigInst`,
`machScalarInst`, `machPureE`, `machConcatE`, `machSigBin`, `machBVLit`, `inlNatLit`, `MachSignOps.sextE/ashrE`, the `where`
function `machLiftScalarN.machLiftConst`) and `senv.natOf` (a field of `StructEnv`, a function value; its result is a `Nat`
that is re-embedded through `inlNatLit`, so it needs no premise). No partial/extern callee remains inside the model.
PROVED: `liftStep_ok` (one step keeps `LetOk 0` if `self` does), `liftN_ok` (any fuel), `liftScalarRange_of`.
PREMISE (named, NOT proved, the ONLY new one): `LiftScalarCorr senv`: shipped `machLiftScalarN ... = some (w, r)` implies
`∃ fuel, liftN fuel ... = some (w, r)` (success only: not refusal, not the reverse direction, not termination). The model is
the text of the shipped function; no equation between them is proved. This REPLACES `LiftScalarRange`, it does not discharge it. -/
namespace Tools.Prototype.LiftScalarModelLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeRangeLetOk Tools.Prototype.BoolMapModelLetOk

/-- The local `bitsW` of `machLiftScalarN`: a width written as a computation (`8 + 8`) is read by the kernel. -/
def liftBitsW (senv : StructEnv) (t : Lean.Expr) : Option Nat := machBits? t <|> (match t with
  | .app (.const ``BitVec _) wE => senv.natOf wE
  | _ => none)

/-- One unfolding of `machLiftScalarN`; recursive calls go through `self`. -/
def liftStep (self : Lean.Expr → Option (Nat × Lean.Expr)) (senv : StructEnv) (dom : Lean.Expr)
    (vars : List (Nat × Lean.Expr)) : Lean.Expr → Option (Nat × Lean.Expr)
  | .bvar i => vars[i]?
  | e@(.app (.app (.app (.app (.app (.app (.const m _) t1) t2) t3) inst) x) y) =>
    let bitsW := liftBitsW senv
    if m == ``HAppend.hAppend then do
      let mw ← bitsW t1
      let nw ← bitsW t2
      unless inst.getAppFn.isConstOf ``BitVec.instHAppendHAddNat do none
      let (mx, x') ← self x
      let (ny, y') ← self y
      if mx != mw || ny != nw then none else
      some (mw + nw, machConcatE dom mw nw x' y')
    else
    match machSigInst m, bitsW t1 with
    | some si, some w =>
      if bitsW t2 == some w && bitsW t3 == some w && machScalarInst m w inst then do
        let (wx, x') ← self x
        let (wy, y') ← self y
        if wx != w || wy != w then none else
        some (w, machSigBin m si dom w x' y')
      else machLiftScalarN.machLiftConst senv dom e
    | _, _ => machLiftScalarN.machLiftConst senv dom e
  | e@(.app (.app (.app (.app (.const ``BitVec.append _) nE) mE) x) y) => do
    if !x.hasLooseBVars && !y.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE <|> senv.natOf nE
    let m ← canonicalNatLitValue? mE <|> senv.natOf mE
    let (wx, x') ← self x
    let (wy, y') ← self y
    if wx != n || wy != m then none else
    some (n + m, machConcatE dom n m x' y')
  | e@(.app (.app (.app (.app (.const ``BitVec.extractLsb' ls) nE) sE) lE) x) => do
    let n ← canonicalNatLitValue? nE <|> senv.natOf nE
    let st ← canonicalNatLitValue? sE <|> senv.natOf sE
    let l ← canonicalNatLitValue? lE <|> senv.natOf lE
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let (wx, x') ← self x
    if wx != n then none else
    if st == 0 && l > n then
      some (l, machConcatE dom (l - n) n (machPureE dom (l - n) (machBVLit (l - n) 0)) x')
    else
    let f := Lean.Expr.lam `x (mkApp (.const ``BitVec []) (inlNatLit n))
      (mkApp4 (.const ``BitVec.extractLsb' ls) (inlNatLit n) (inlNatLit st) (inlNatLit l) (.bvar 0))
      .default
    some (l, mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero, .zero]) dom
      (mkApp (.const ``BitVec []) (inlNatLit n)) (mkApp (.const ``BitVec []) (inlNatLit l)) f x')
  | e@(.app (.app (.const ``BitVec.not _) nE) x) => do
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← self x
    if wx != n then none else
    some (n, machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom n
      (machPureE dom n (machBVLit n (2 ^ n - 1))) x')
  | e@(.app (.app (.app (.const ``BitVec.signExtend _) wE) vE) x) => do
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let w ← canonicalNatLitValue? wE
    let v ← canonicalNatLitValue? vE <|> senv.natOf vE
    let (wx, x') ← self x
    if wx != w || w == 0 || v ≤ w then none else
    some (v, Sparkle.Compiler.MachSignOps.sextE inlNatLit (machConcatE dom) dom (v - w) w x')
  | e@(.app (.app (.app (.const ``BitVec.sshiftRight _) nE) x) s) => do
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    if n == 0 then none else
    let (wx, x') ← self x
    if wx != n then none else
    let y' ← match s with
      | .app (.app (.const ``BitVec.toNat _) mE) y => do
        if canonicalNatLitValue? mE != some n then none else
        let (wy, y') ← self y
        if wy != n then none else some y'
      | _ => do
        if s.hasLooseBVars then none else
        let k ← canonicalNatLitValue? s <|> senv.natOf s
        if k ≥ 2 ^ n then none else some (machPureE dom n (machBVLit n k))
    some (n, Sparkle.Compiler.MachSignOps.ashrE inlNatLit
      (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b) dom n x' y')
  | .app (.app (.app (.const ``Sparkle.Core.Signal.ashr _) nE) x) y =>
    self (mkApp3 (.const ``BitVec.sshiftRight []) nE x (mkApp2 (.const ``BitVec.toNat []) nE y))
  | e@(.app (.app (.app (.const ``Neg.neg _) (.app (.const ``BitVec _) nE)) _) x) => do
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← self x
    if wx != n then none else
    some (n, machSigBin ``HSub.hSub ``Sparkle.Core.Signal.instHSubSignalBitVec dom n
      (machPureE dom n (machBVLit n 0)) x')
  | e@(.app (.app (.app (.const ``Complement.complement _) (.app (.const ``BitVec _) nE)) _) x) => do
    if !x.hasLooseBVars then machLiftScalarN.machLiftConst senv dom e else
    let n ← canonicalNatLitValue? nE
    let (wx, x') ← self x
    if wx != n then none else
    some (n, machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom n
      (machPureE dom n (machBVLit n (2 ^ n - 1))) x')
  | e => machLiftScalarN.machLiftConst senv dom e

/-- The model: `liftStep` iterated `fuel` times. -/
def liftN (senv : StructEnv) (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) :
    Nat → Lean.Expr → Option (Nat × Lean.Expr)
  | 0, _ => none
  | k + 1, e => liftStep (liftN senv dom vars k) senv dom vars e

theorem sextE_ok {natE : Nat → Lean.Expr} {concatE : Nat → Nat → Lean.Expr → Lean.Expr → Lean.Expr}
    (hnat : ∀ k, LetOk 0 (natE k) = true)
    (hcat : ∀ m n a b, LetOk 0 a = true → LetOk 0 b = true → LetOk 0 (concatE m n a b) = true)
    {dom x : Lean.Expr} (hd : LetOk 0 dom = true) (hx : LetOk 0 x = true) (k w : Nat) :
    LetOk 0 (Sparkle.Compiler.MachSignOps.sextE natE concatE dom k w x) = true := by
  unfold Sparkle.Compiler.MachSignOps.sextE
  refine hcat _ _ _ _ ?_ hx
  simp [Sparkle.Compiler.MachSignOps.msbE, Sparkle.Compiler.MachSignOps.fillE,
      Sparkle.Compiler.MachSignOps.bvT, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB, LetOk, hnat, hd, hx]

theorem liftConst_ok {senv : StructEnv} {dom e : Lean.Expr} {w : Nat} {r : Lean.Expr} (hd : LetOk 0 dom = true)
    (he : LetOk 0 e = true) (h : machLiftScalarN.machLiftConst senv dom e = some (w, r)) : LetOk 0 r = true := by
  unfold machLiftScalarN.machLiftConst at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact machPureE_ok _ hd he
    · cases h

theorem liftStep_ok {self : Lean.Expr → Option (Nat × Lean.Expr)} {senv : StructEnv} {dom : Lean.Expr}
    {vars : List (Nat × Lean.Expr)} (hd : LetOk 0 dom = true) (hv : ∀ p ∈ vars, LetOk 0 p.2 = true)
    (hs : ∀ x w r, LetOk 0 x = true → self x = some (w, r) → LetOk 0 r = true) :
    ∀ (e : Lean.Expr) (w : Nat) (r : Lean.Expr), LetOk 0 e = true →
      liftStep self senv dom vars e = some (w, r) → LetOk 0 r = true := by
  intro e w r he h
  unfold liftStep at h
  split at h
  · exact hv _ (List.mem_of_getElem? h)
  · rename_i e0 m us t1 t2 t3 inst x y
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    have hy : LetOk 0 y = true := by simp [LetOk] at he; simp [he]
    dsimp only at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨mw, -, nw, -, h⟩ := h
      split at h
      · simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨mx, x'⟩, hx', h⟩ := h
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨ny, y'⟩, hy', h⟩ := h
        split at h
        · cases h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact machConcatE_ok _ _ hd (hs _ _ _ hx hx') (hs _ _ _ hy hy')
      · simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨a, ha, -⟩ := h
        cases ha
    · rcases hsi : machSigInst m with _ | si
      · simp only [hsi] at h
        exact liftConst_ok hd he h
      · rcases hb : liftBitsW senv t1 with _ | w0
        · simp only [hsi, hb] at h
          exact liftConst_ok hd he h
        · simp only [hsi, hb] at h
          by_cases hc : (liftBitsW senv t2 == some w0 && liftBitsW senv t3 == some w0 && machScalarInst m w0 inst) = true
          · rw [if_pos hc] at h
            simp only [bind, Option.bind_eq_some_iff] at h
            obtain ⟨⟨wx, x'⟩, hx', h⟩ := h
            simp only [bind, Option.bind_eq_some_iff] at h
            obtain ⟨⟨wy, y'⟩, hy', h⟩ := h
            split at h
            · cases h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact machSigBin_ok hd _ _ _ (hs _ _ _ hx hx') (hs _ _ _ hy hy')
          · rw [if_neg hc] at h
            exact liftConst_ok hd he h
  · rename_i e0 us nE mE x y
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    have hy : LetOk 0 y = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, m, -, ⟨wx, x'⟩, hx', h⟩ := h
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨wy, y'⟩, hy', h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact machConcatE_ok _ _ hd (hs _ _ _ hx hx') (hs _ _ _ hy hy')
  · rename_i e0 ls nE sE lE x
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨n, -, st, -, l, -, h⟩ := h
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨wx, x'⟩, hx', h⟩ := h
      have hx1 := hs _ _ _ hx hx'
      split at h
      · cases h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact machConcatE_ok _ _ hd (machPureE_ok _ hd (machBVLit_ok _ _)) hx1
        · dsimp only at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simp [LetOk, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, inlNatLit, letOk_natLit, hd, hx1]
  · rename_i e0 us nE x
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, ⟨wx, x'⟩, hx', h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) (hs _ _ _ hx hx')
  · rename_i e0 us wE vE x
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, v, -, ⟨wx, x'⟩, hx', h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact sextE_ok (fun k => by simp [inlNatLit, mkApp3, mkApp, LetOk, letOk_natLit])
          (fun m n a b ha hb => machConcatE_ok m n hd ha hb) hd (hs _ _ _ hx hx') _ _
  · rename_i e0 us nE x s
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    have hs0 : LetOk 0 s = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, h⟩ := h
      split at h
      · cases h
      · simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨wx, x'⟩, hx', h⟩ := h
        have hx1 := hs _ _ _ hx hx'
        have hfin : ∀ y' k, LetOk 0 y' = true →
            LetOk 0 (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
              (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom k a b) dom k x' y') = true :=
          fun y' k hy => ashrE_ok _ _ (fun k => by simp [inlNatLit, mkApp3, mkApp, LetOk, letOk_natLit])
            (fun _ _ _ ha hb => machSigBin_ok hd _ _ _ ha hb) hd hx1 hy k
        split at h
        · cases h
        · dsimp only at h
          split at h
          · rename_i mE y
            have hy : LetOk 0 y = true := by simp [LetOk] at hs0; simp [hs0]
            split at h
            · simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨a, ha, -⟩ := h
              cases ha
            · simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨⟨wy, y'⟩, hy', h⟩ := h
              have hy1 := hs _ _ _ hy hy'
              split at h
              · simp only [bind, Option.bind_eq_some_iff] at h
                obtain ⟨a, ha, -⟩ := h
                cases ha
              · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl, -, rfl⟩ := h
                exact hfin _ _ hy1
          · split at h
            · simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨a, ha, -⟩ := h
              cases ha
            · simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨k, -, h⟩ := h
              split at h
              · simp only [bind, Option.bind_eq_some_iff] at h
                obtain ⟨a, ha, -⟩ := h
                cases ha
              · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl, -, rfl⟩ := h
                exact hfin _ _ (machPureE_ok _ hd (machBVLit_ok _ _))
  · rename_i e0 nE x y
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    have hy : LetOk 0 y = true := by simp [LetOk] at he; simp [he]
    have hn : LetOk 0 nE = true := by simp [LetOk] at he; simp [he]
    exact hs _ _ _ (by simp [LetOk, mkApp3, mkApp2, mkApp, hx, hy, hn]) h
  · rename_i e0 us us' nE a x
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, ⟨wx, x'⟩, hx', h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) (hs _ _ _ hx hx')
  · rename_i e0 us us' nE a x
    have hx : LetOk 0 x = true := by simp [LetOk] at he; simp [he]
    split at h
    · exact liftConst_ok hd he h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨n, -, ⟨wx, x'⟩, hx', h⟩ := h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) (hs _ _ _ hx hx')
  · exact liftConst_ok hd he h

theorem liftN_ok {senv : StructEnv} {dom : Lean.Expr} {vars : List (Nat × Lean.Expr)} (hd : LetOk 0 dom = true)
    (hv : ∀ p ∈ vars, LetOk 0 p.2 = true) :
    ∀ (k : Nat) (e : Lean.Expr) (w : Nat) (r : Lean.Expr), LetOk 0 e = true →
      liftN senv dom vars k e = some (w, r) → LetOk 0 r = true := by
  intro k
  induction k with
  | zero => intro e w r _ h; simp [liftN] at h
  | succ k ih => intro e w r he h; exact liftStep_ok hd hv ih e w r he h

/-- PREMISE (named, NOT proved; the ONLY new one): whenever the shipped `partial def machLiftScalarN` returns `some (w, r)`,
the model returns the same pair at some fuel. Success direction only (not refusal, not the reverse, not termination); the two
function bodies are the same text, but no equation between them is proved. -/
def LiftScalarCorr (senv : StructEnv) : Prop :=
  ∀ (dom : Lean.Expr) (vars : List (Nat × Lean.Expr)) (e : Lean.Expr) (w : Nat) (r : Lean.Expr),
    machLiftScalarN senv dom vars e = some (w, r) → ∃ fuel, liftN senv dom vars fuel e = some (w, r)

/-- `LiftScalarRange` from the ONE correspondence lemma `LiftScalarCorr` (a replacement, not a discharge). -/
theorem liftScalarRange_of {senv : StructEnv} (hc : LiftScalarCorr senv) : LiftScalarRange senv := by
  intro dom vars e w r hd hv he h
  obtain ⟨k, hk⟩ := hc dom vars e w r h
  exact liftN_ok hd hv k e w r he hk

/-- `machineShapeN_lets''_noBM` with `LiftScalarRange` replaced by `LiftScalarCorr`. -/
theorem machineShapeN_lets''_noLS {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees)
    (hraw : RawNodeRange senv) (hlc : LiftScalarCorr senv) (hbc : BoolMapCorr senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets''_noBM hroot hlift hinst1 hsig hz hraw (liftScalarRange_of hlc) hbc hpe hstart h

#print axioms liftStep_ok
#print axioms liftN_ok
#print axioms liftScalarRange_of
#print axioms machineShapeN_lets''_noLS

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''_noLS
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "LiftScalarCorr",
    "BoolMapCorr", "Eq", "StartDomOk", "Eq"])

end Tools.Prototype.LiftScalarModelLetOk
