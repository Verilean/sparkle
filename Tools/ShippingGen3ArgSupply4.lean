import Tools.ShippingGen3ArgSupply3   -- batch 3: GoodE/goodE_readF, EntryKindOk/EnvKindOkE/CallPreKE/GoodKE, closed arms
import Tools.ShippingSparseCasesTac   -- unfold_matchers_aux / dsimp_sparse_aux (the `regView?` matcher, as LetsReaderInvPure2)
set_option autoImplicit false
-- WRITTEN, NOT BUILT (batch 4; no lake/lean run by the author). No `sorry`, no `axiom`, no `native_decide`.

/-! # SRC-ARGW batch 4: G2 / G4 argument lemmas and E arms, G3 / G14 / G21 audit, LK1 induction SKELETON

(scripts/gen3/SRC_ARGW_SUPPLY_FREEZE.md rev3 §3.7 option (b), rev3.1 notes, rev3.2 status.)

CONDITIONAL INTERMEDIATE WORK ONLY. NOT an L-RUN1 discharge, NOT L-FG supply, NOT FG completion (§1.3). The LK1
statement below is a SKELETON: it is proved only FROM the open arms, which are explicit named premises. Nothing here
is a reader run of a corpus declaration (the loop-root probe is Tests/Gen3/LoopRootProbe.lean, logs only). No shared
definition, no compiler file, no FG statement is edited.

## 1. Argument lemmas
* `regView?_all` (G2): every component the bare-register view returns that the reader converts (`dom`, `x`) satisfies
  any predicate all of `args` satisfy. `regView?` is one of the two matchers v4.32.1 cannot split (name literal +
  array literal); the proof is the BUILT technique of `regView_ok` (Tools/ShippingLetsReaderInvPure2.lean:17-50)
  with `LetOk n` replaced by an arbitrary `P` (same tactic script, same case structure).
* `machRunApp?_spine`, `machRunApp?_readSub` (G4): the run's domain is a spine argument and its body is under the
  last argument's `lam` binder (`ReadSub.lamB`), at the call's own `Δ`.

## 2. E arms written here (each conditional on `GoodKE` of the table; `GoodE` where a second call is issued)
* **G2** `satKE_conv_bareReg` (both calls: `dom` at `st`, `x` at the slot-pushed state; `bareRegs` hit: `st`).
* **G3** `satKE_conv_loopRead`, `satKE_conv_readV` (state unchanged).
* **G4** conv dispatch `satKE_conv_nestedCall` (the kept call site = `.app f a`, ReadSub from the conv call) and the
  body `satKE_nested` (domain call, shared probe via `findSomeO`, fresh `machReserve` + chain under `.regs base`).
* **G5 / G6 dispatch** (NOT the bodies): `satKE_conv_instCall` (`pre_of_instCallP`), `satKE_conv_instSCall`
  (`pre_of_instCallSP`), `satKE_conv_memCall` (`pre_of_memP`, `InstSite .mem`, then `instStruct := true`).
* **G14** `satKE_conv_fvar` / `_mvar` / `_sort` / `_const` / `_lit` (default arm, state unchanged).
* Dispatchers: `conv_app_satKE` (the eight recogniser outcomes of FD:304-352), `conv_letE_satKE`,
  `conv_satKE` (all twelve `Expr` constructors), `chain_satKE`, `chain_letE_satKE`, `loopBody_satKE`.
* Bookkeeping: `satK_domGuard`, `satK_pure_ite`, `satK_findSomeO`, `satK_nestedProbe`, `readInv_reserve`,
  `readInv_instStruct`, `eq_zero_of_not_or4`.

## 3. Audit G3 / G14 / G21 (what `ConvKind` must supply; §3.3 `ConvKind`, §3.4 table)
`HKL.var` + `phKind_slot` give `HK (phKind p.bs st) (machSlot i) k ↔ st.kinds[i]? = some k`.
* **G3a** `machLoopRead?` (FD:322-324): LK1 obligation none — CLOSED (`satKE_conv_loopRead`). TY supply at the output
  `machSlot (b + j)` (an env entry `.state b n`, `Signal.fst`/`Signal.snd` chain): `st.kinds[b + j]? = some k` for the
  source kind `k` of the projection. NOT suppliable from the current invariants: `EnvKindOkE` constrains `.state b n`
  only at a TYPED binder (then `n = 1`); a tuple binder has Δ entry `none` (E:2337-2343), so nothing relates
  `st.kinds[b .. b+n)` to the tuple's component types. Needs NEW: a tuple-aware entry invariant (component kinds of
  the loop binder's `Signal dom (T₀ × …)` at `kinds[b + j]`) + a source fact that the loop's register kinds
  (`machLoopRegs` / `loopRegKind`, FD:567-569) are those component kinds (generalising `LoopSrcKinds`).
* **G3b** `machReadV` (FD:346-348): LK1 none — CLOSED (`satKE_conv_readV`). TY supply at `machSlot i`, `i` from a
  `.handle i` / `.regs p` entry (nested `runCircuitH` handles): `st.kinds[i]? = some k`. Kinds come from
  `machReserve`'s `machSlotKinds (zetaAll αs)` (opaque `zetaAll`, E:3705). Needs NEW: a source fact relating the run's
  slot-type list `αs` to the handle projections' source kinds, and an invariant tying `.regs p`/`.handle i` entries to
  the reserved slots. Neither exists.
* **G14** default arm (FD:382): LK1 none — CLOSED (`satKE_conv_fvar` … `_lit`). TY supply: `HK (phKind p.bs st) e k`
  for the UNCHANGED atom `e` from `SK (Δ ++ inCtx p) e k`; `phKind` of a non-placeholder is `none`, so this needs a
  NEW SK→HK law at atoms (or a vacuity proof that `SK` kinds no `.const`/`.lit`/`.sort` atom at a non-domain kind;
  `.fvar`: source atoms are not shown placeholder-free). Not closed (TY side).
* **G21** wrapper (FS:207-241; OUTSIDE `step`, so outside the table induction §4): start state `{}` (`readInv_empty`,
  A2) or `machReserve`'s from `{}` (`readInv_reserve`, here) — CLOSED; S1 `ReadSub` of `m.run?`'s dom/body through
  `machRoot`'s peeled root lets and the wrap case (FS:146-148) — NOT written; root-let pushes `.val x` (with the
  `machBindLetNamed` variant when loops are non-empty, FS:224-225) — as G11; loop root-lets — as G12/G20. No `ConvKind`
  obligation beyond G11's (at `v`) and G12's. Not closed.
* **G2** TY supply (not audited before): the fresh result `machSlot base` has `st'.kinds[base] = machSlotKind? α`
  (pushed); the supplier needs `SK Γ e k → machSlotKind? α = some k` (a register source fact). The `bareRegs` hit
  (`machSlot k'` for an `==`-equal earlier `e`) additionally needs a NEW state invariant ("each `bareRegs` entry
  `(e₀, i)` has `kinds[i] = machSlotKind?` of `e₀`'s type") + `SK` respecting `==` (D1). **G4** TY supply: the nested
  result `v` (chain value) kind — still NOT AUDITED.

## 4. LK1 skeleton (§3.4 LK1, table form)
`LK1Open` collects the OPEN arms as named premises (`ArmG5`, `ArmG6`, `ArmG11`, `ArmG12conv`, `ArmG12chain`,
`ArmG17user`, `ArmG18`, `ArmG20`); every other arm is plugged in by a written lemma (batch 2/3/4).
`step_goodKE` + `goodKE_readF_of_open : LK1Open … → ∀ n, GoodKE … (readF senv n)` (fuel induction, `GoodE` from
`goodE_readF`). This is NOT a completion claim: it says exactly that the eight listed premises are what remains for
LK1's table form (G21 and the run form `machineShapeF_final_readInv` are not covered: they are wrapper-level).
-/
namespace Tools.ShippingGen3ArgSupply4
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingGen3ArgSupply (phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingReaderFuelProv (InstProv CallPreP pre_of_instCallP pre_of_instCallSP pre_of_memP instProv_struct)
open Tools.ShippingReaderLenOk (machReserve_some reserved)
open Tools.ShippingGen3ArgSupply2
open Tools.ShippingGen3ArgSupply3
open Tools.ShippingSparseCasesTac

/-! ## 1. Argument lemmas -/

set_option maxHeartbeats 16000000 in
/-- **G2 argument lemma.** The bare-register view returns spine arguments (proof script of the BUILT `regView_ok`,
Tools/ShippingLetsReaderInvPure2.lean:17-50, with `LetOk n` generalised to `P`). -/
theorem regView?_all (P : Lean.Expr → Prop) (fn : Lean.Expr) (args : Array Lean.Expr) (d α i x : Lean.Expr)
    (hall : ∀ a ∈ args, P a) (h : regView? fn args = some (d, α, i, x)) :
    P d ∧ P x := by
  revert h
  unfold regView?
  rcases args with ⟨L⟩
  cases fn with
  | const nm us =>
    rcases nm with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    all_goals first
      | (intro hh; cases hh; done)
      | (subst_vars; intro hh; cases hh; done)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, L'⟩⟩⟩⟩⟩ <;>
          first
            | (intro hh; cases hh; done)
            | (subst_vars; intro hh; cases hh; done)
            | (subst_vars; intro hh
               injection hh with h1
               injection h1 with hd h2
               injection h2 with hα h3
               injection h3 with hi hx
               subst hd
               subst hx
               exact ⟨hall a1 (by simp), hall a4 (by simp)⟩)
            | (exfalso; simp at *; done)
            | (exfalso; simp at *; omega))
  | _ => intro hh; cases hh

/-- `regView?_all` at `ReadSub` (the bare register's `dom` and `x` are reader inputs at the conv call's `Δ`). -/
theorem regView?_readSub {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {f a : Lean.Expr}
    {dom α init x : Lean.Expr} (hR : ReadSub senv r Δ (.app f a))
    (h : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x)) :
    ReadSub senv r Δ dom ∧ ReadSub senv r Δ x :=
  regView?_all (ReadSub senv r Δ) _ _ dom α init x (readSub_getAppArgs hR) h

/-- **G4 argument lemma (spine).** `machRunApp?` (E:3675-3679) succeeds only at a `runCircuitH` spine whose last
argument is a `lam` over the body. -/
theorem machRunApp?_spine {e dom αs is body : Lean.Expr} (h : machRunApp? e = some (dom, αs, is, body)) :
    ∃ (hd x1 x2 x3 x4 : Lean.Expr) (n : Name) (t : Lean.Expr) (bi : BinderInfo),
      inlSpine e [] = (hd, [dom, αs, x1, x2, x3, x4, is, .lam n t body bi]) := by
  first
    -- route 1 (as `machInstCall?_args`, A2): split on the spine itself, keep the splitter's equation
    | (unfold machRunApp? at h
       split at h
       all_goals first
         | (cases h; done)
         | (injection h with h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            first
              | exact ⟨_, _, _, _, _, _, _, _, by assumption⟩
              | (rename_i heq0; exact ⟨_, _, _, _, _, _, _, _, heq0⟩)))
    -- route 2 (as `runApp_ok`, Tools/ShippingLetsReaderInvPure.lean:85-97): generalise the spine first
    | (unfold machRunApp? at h
       generalize hsp : inlSpine e [] = sp at h
       obtain ⟨fn, args⟩ := sp
       split at h
       all_goals first
         | (cases h; done)
         | (injection h with h
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            first
              | exact ⟨_, _, _, _, _, _, _, _, hsp⟩
              | exact ⟨_, _, _, _, _, _, _, _, by assumption⟩
              | (simp only [Prod.mk.injEq] at *
                 obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
                 exact ⟨_, _, _, _, _, _, _, _, hsp⟩)))

/-- **G4 argument lemma.** The run's domain is a reader input at `Δ`; its body is one under the last argument's
binder (`ReadSub.lamB`). -/
theorem machRunApp?_readSub {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {e dom αs is body : Lean.Expr}
    (hR : ReadSub senv r Δ e) (h : machRunApp? e = some (dom, αs, is, body)) :
    ReadSub senv r Δ dom ∧ ∃ t : Lean.Expr, ReadSub senv r (mixedGateBinderKind? t :: Δ) body := by
  obtain ⟨hd, x1, x2, x3, x4, n, t, bi, hsp⟩ := machRunApp?_spine h
  have hs := readSub_inlSpine e [] hR (fun _ hx => by cases hx)
  rw [hsp] at hs
  exact ⟨hs dom (by simp), t, ReadSub.lamB (hs (.lam n t body bi) (by simp))⟩

/-! ## 2. Bookkeeping -/

theorem eq_zero_of_not_or4 {d : Nat} {b1 b2 b3 : Bool} (h : ¬ ((d != 0 || b1 || b2 || b3) = true)) : d = 0 := by
  cases d with
  | zero => rfl
  | succ k => exact absurd (by first | rfl | simp | decide) h

section CombK
variable {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt α]

theorem satK_domGuard {o : Option Lean.Expr} {dom' : Lean.Expr} {k : BM (Option α)}
    (hk : SatK HK senv p h k) : SatK HK senv p h (domGuard o dom' k) := by
  cases o with
  | none => exact hk
  | some d0 =>
    first
      | exact satK_ite2 (fun _ => satK_failO) (fun _ => hk)
      | (simp only [domGuard]; exact satK_ite2 (fun _ => satK_failO) (fun _ => hk))

theorem satK_pure_ite {c : Prop} [Decidable c] {a : α} (ha : StK HK senv p a) :
    SatK HK senv p h (FM.pure (if c then some a else none)) := by
  by_cases hc : c
  · rw [if_pos hc]
    exact satK_okO ha
  · rw [if_neg hc]
    exact satK_failO

end CombK

theorem satK_findSomeO {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt β]
    {f : α → BM (Option β)} (hf : ∀ a, SatK HK senv p h (f a)) :
    ∀ (l : List α), SatK HK senv p h (findSomeO f l)
  | [] => satK_failO
  | a :: l => by
    refine satK_bind ?_
    intro r hr
    cases r with
    | none => exact satK_findSomeO hf l
    | some b => exact satK_okO (hf a b hr)

/-- `machReserve` (E:3703-3717) keeps `ReadInv`: only `kinds`/`inits`/`names`/`dom`/`runs` change. -/
theorem readInv_reserve {HK : PhKinding} {senv : StructEnv} {p : ShapePre} (HKL : PhKindingLaws HK)
    {natOf : Lean.Expr → Option Nat} {dom' αs initsE body : Lean.Expr} {st : MachRead} {base : Nat}
    {st' : MachRead} (h : ReadInv HK senv p st)
    (hr : machReserve natOf dom' αs initsE body st = some (base, st')) : ReadInv HK senv p st' := by
  have hx := machReserve_ext hr
  obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hr
  subst hst
  exact readInv_congr HKL h hx rfl rfl rfl rfl rfl

/-- `instStruct := true` (the memory arm FD:345, `instEntry .bool`) keeps `ReadInv` (`instProv_struct`). -/
theorem readInv_instStruct {HK : PhKinding} {senv : StructEnv} {p : ShapePre} (HKL : PhKindingLaws HK)
    {st : MachRead} (h : ReadInv HK senv p st) : ReadInv HK senv p { st with instStruct := true } := by
  obtain ⟨hP, hL, hA⟩ := h
  refine ⟨instProv_struct hP rfl rfl rfl rfl,
    letKindOk_sameLets HKL hL (phExt_instStruct (phExt_refl st) true) rfl, ?_⟩
  intro k c js r kinds hk hsk
  exact hA k c js r kinds hk hsk

/-! ## 3. G2: the bare register (FD:304-320) -/

/-- **G2** (conv bare register): `bareRegs` hit returns `st`; otherwise `dom` at `st`, then `x` at the slot-pushed
state (`envKindOkE_ext` along `PhExt`), result state `{ … with ws := … }`. -/
theorem satKE_conv_bareReg {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    {dom α init x : Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x)) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  obtain ⟨hRdom, hRx⟩ := regView?_readSub hR h1
  first
    | simp only [convStep, h1]
    | (unfold convStep; dsimp only; simp only [h1])
  refine satK_ite2 (fun _ => satK_failO) (fun hc => ?_)
  have hd : d = 0 := by
    first
      | exact eq_zero_of_not_or4 hc
      | (cases d with
         | zero => rfl
         | succ k => exact absurd (by simp) hc)
  subst hd
  split
  · exact satK_okO hst
  · refine satK_optK ?_
    intro kind _
    refine satK_optK ?_
    intro initN _
    have hpre1 : CallPreKE HK senv p en (Call.conv env 0 dom st) := ⟨Δ, hEnv, hRdom⟩
    refine satK_bindOE hE (satK_cConvE hG hpre1 hst) (cConv_phExt hE) ?_
    rintro ⟨dom', st1⟩ (hs1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
    refine satK_domGuard ?_
    refine satK_bindO (satK_cConvE hG ?_ ?_) ?_
    · exact ⟨Δ, envKindOkE_ext HKL hEnv (phExt_trans hx1 (phExt_bareRegister (phExt_refl st1) _ _ _ _ _ _)),
        hRx⟩
    · exact readInv_congr HKL hs1 (phExt_bareRegister (phExt_refl st1) _ _ _ _ _ _) rfl rfl rfl rfl rfl
    · rintro ⟨x', st2⟩ (hs2 : ReadInv HK senv p st2)
      exact satK_okO (readInv_ws HKL hs2 _)

/-! ## 4. G3: slot reads (FD:322-324, :346-348; state unchanged) -/

/-- **G3a** (`machLoopRead?`). -/
theorem satKE_conv_loopRead {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead} (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    {i : Nat} (h2 : machLoopRead? env d (.app f a) = some i) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep, h1, h2]
    | (unfold convStep; dsimp only; simp only [h1, h2])
  refine satK_pure ?_
  intro r hr
  split at hr
  · injection hr with hr1
    subst hr1
    exact hst
  · cases hr

/-- **G3b** (`machReadV`, after the six recognisers before it fail). -/
theorem satKE_conv_readV {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead} (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none) (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
      (.app f a) = none)
    {i : Nat} (h7 : machReadV env d (.app f a) = some i) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  first
    | simp only [convStep, h1, h2, h3, h4, h5, h6, h7]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3, h4, h5, h6, h7])
  refine satK_pure ?_
  intro r hr
  split at hr
  · injection hr with hr1
    subst hr1
    exact hst
  · cases hr

/-! ## 5. G4: the nested machine (FD:326-328 dispatch, FD:385-410 body) -/

/-- **G4 dispatch** (conv → `cNested`): the kept call site is `.app f a` itself. -/
theorem satKE_conv_nestedCall {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    {dom αs initsE body : Lean.Expr} (h3 : machRunApp? (.app f a) = some (dom, αs, initsE, body)) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  first
    | simp only [convStep, h1, h2, h3]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3])
  refine satK_ite2 (fun _ => satK_failO) (fun hd0 => ?_)
  have hd : d = 0 := eq_zero_of_not_bne hd0
  subst hd
  exact fun r hr => hG (Call.nested env dom αs initsE body st) ⟨Δ, Lean.Expr.app f a, hEnv, hR, h3⟩ hst r hr

/-- One sharing probe (FD:385-393): the chain at the probe's state under `.regs base`; the answer's state is the
chain's. -/
theorem satK_nestedProbe {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h) {env : List MachVal} {dom' αs initsE body : Lean.Expr} {st : MachRead}
    (hpreB : ∀ base : Nat, CallPreKE HK senv p en (Call.chain (MachVal.regs base :: env) body st))
    (hst : ReadInv HK senv p st) :
    ∀ q, SatK HK senv p h (nestedProbe env dom' αs initsE body st q) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  refine satK_ite2 (fun _ => ?_) (fun _ => satK_failO)
  refine satK_bind ?_
  intro r hr
  rcases r with _ | ⟨ws', v', st'⟩
  · exact satK_failO
  · have h' : ReadInv HK senv p st' := satK_cChainE hG (hpreB base) hst (ws', v', st') hr
    refine satK_pure_ite ?_
    exact h'

/-- **G4 body** (`nestedStep`, FD:397-410). -/
theorem satKE_nested {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {dom αs initsE body : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.nested env dom αs initsE body st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (nestedStep senv env dom αs initsE body st) := by
  obtain ⟨Δ, e, hEnv, hR, hrun⟩ := hpre
  obtain ⟨hRdom, t, hRbody⟩ := machRunApp?_readSub hR hrun
  refine satK_ite2 (fun _ => satK_failO) (fun _ => ?_)
  have hpre1 : CallPreKE HK senv p en (Call.conv env 0 dom st) := ⟨Δ, hEnv, hRdom⟩
  refine satK_bindOE hE (satK_cConvE hG hpre1 hst) (cConv_phExt hE) ?_
  rintro ⟨dom', st1⟩ (hs1 : ReadInv HK senv p st1) (hx1 : PhExt st st1)
  have hpreB : ∀ (base : Nat) (s : MachRead), PhExt st1 s →
      CallPreKE HK senv p en (Call.chain (MachVal.regs base :: env) body s) :=
    fun base s hx => ⟨_, envKindOkE_cons (mixedGateBinderKind? t) (MachVal.regs base) (fun _ _ _ => trivial)
      (envKindOkE_ext HKL hEnv (phExt_trans hx1 hx)), hRbody⟩
  refine satK_bind ?_
  intro shared hsh
  rcases shared with _ | r
  · -- fresh machine: `machReserve`, then the chain under `.regs base` with `inInner := true`
    refine satK_optK ?_
    rintro ⟨base, st2⟩ hres
    have hs2 : ReadInv HK senv p st2 := readInv_reserve HKL hs1 hres
    have hx2 : PhExt st1 st2 := machReserve_ext hres
    have hpreC : CallPreKE HK senv p en
        (Call.chain (MachVal.regs base :: env) body { st2 with inInner := true }) :=
      hpreB base _ (phExt_trans hx2 (phExt_inInner (phExt_refl st2) true))
    have hsC : ReadInv HK senv p { st2 with inInner := true } :=
      readInv_congr HKL hs2 (phExt_inInner (phExt_refl st2) true) rfl rfl rfl rfl rfl
    refine satK_bindO (satK_cChainE hG hpreC hsC) ?_
    rintro ⟨ws, v, st3⟩ (hs3 : ReadInv HK senv p st3)
    exact satK_okO (readInv_congr HKL hs3 (phExt_nestedClose (phExt_refl st3) _ _ _) rfl rfl rfl rfl rfl)
  · -- shared machine: the probe's answer
    refine satK_okO ?_
    exact satK_findSomeO (satK_nestedProbe hG (fun base => hpreB base st1 (phExt_refl st1)) hs1) _ r hsh

/-! ## 6. G5 / G6 dispatch at the conv arm (FD:330-345; the BODIES `instStep` / `instSStep` stay OPEN) -/

/-- **G5 dispatch, `.ord`** (conv → `cInst … .ord`, `pre_of_instCallP`). -/
theorem satKE_conv_instCall {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    {c : Name} {ks : List MixedGateBinder} {res : MixedGateBinder} {args : List Lean.Expr}
    (h4 : machInstCall? senv (.app f a) = some (c, ks, res, args)) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  first
    | simp only [convStep, h1, h2, h3, h4]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3, h4])
  refine satK_ite2 (fun _ => satK_failO) (fun hd0 => ?_)
  have hd : d = 0 := eq_zero_of_not_bne hd0
  subst hd
  exact fun r hr => hG (Call.inst env c .ord ks res args st)
    ⟨pre_of_instCallP h4, Δ, Lean.Expr.app f a, hEnv, hR, h4⟩ hst r hr

/-- **G6 dispatch** (conv → `cInstS`, `pre_of_instCallSP`). -/
theorem satKE_conv_instSCall {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodKE HK senv p en h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none)
    {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (h5 : machInstCallS? senv (.app f a) = some (c, ks, ty, args)) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  first
    | simp only [convStep, h1, h2, h3, h4, h5]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3, h4, h5])
  refine satK_ite2 (fun _ => satK_failO) (fun hd0 => ?_)
  have hd : d = 0 := eq_zero_of_not_bne hd0
  subst hd
  have hS : senv.instS c = some (ks, ty) := pre_of_instCallSP (env := env) (st := st) h5
  exact fun r hr => hG (Call.instS env c ks ty args st)
    ⟨hS, Δ, Lean.Expr.app f a, hEnv, hR, h5⟩ hst r hr

/-- **G5 dispatch, memory** (conv → `cInst … (.mem …)`, `pre_of_memP`, `InstSite .mem`; then `instStruct := true`). -/
theorem satKE_conv_memCall {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none) (h5 : machInstCallS? senv (.app f a) = none)
    {combo : Bool} {aw dw : Nat} {dom : Lean.Expr} {ops : List Lean.Expr}
    (h6 : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
      (.app f a) = some (combo, aw, dw, dom, ops)) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  obtain ⟨Δ, hEnv, hR⟩ := hpre
  first
    | simp only [convStep, h1, h2, h3, h4, h5, h6]
    | (unfold convStep; dsimp only; simp only [h1, h2, h3, h4, h5, h6])
  refine satK_ite2 (fun _ => satK_failO) (fun hd0 => ?_)
  have hd : d = 0 := eq_zero_of_not_bne hd0
  subst hd
  have hc : SatK HK senv p h (cInst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
      (.mem combo aw dw) [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st) :=
    fun r hr => hG (Call.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
      (.mem combo aw dw) [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st)
      ⟨pre_of_memP h6, Δ, Lean.Expr.app f a, hEnv, hR, ⟨dom, ops, h6, rfl, rfl, rfl, rfl⟩⟩ hst r hr
  refine satK_bindO hc ?_
  rintro ⟨v, st1⟩ (hs1 : ReadInv HK senv p st1)
  exact satK_okO (readInv_instStruct HKL hs1)

/-! ## 7. G14: the default arm (FD:382, `okO (e, st)`) -/

theorem satKE_conv_atom {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} (hst : ReadInv HK senv p st)
    (he : convStep senv env d e st = okO (e, st)) : SatK HK senv p h (convStep senv env d e st) := by
  rw [he]
  exact satK_okO hst

theorem satKE_conv_fvar {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {x : FVarId} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.fvar x) st) :=
  satKE_conv_atom hst (by first | rfl | simp [convStep])

theorem satKE_conv_mvar {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {m : MVarId} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.mvar m) st) :=
  satKE_conv_atom hst (by first | rfl | simp [convStep])

theorem satKE_conv_sort {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {u : Level} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.sort u) st) :=
  satKE_conv_atom hst (by first | rfl | simp [convStep])

theorem satKE_conv_const {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {c : Name} {us : List Level} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.const c us) st) :=
  satKE_conv_atom hst (by first | rfl | simp [convStep])

theorem satKE_conv_lit {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {l : Literal} {st : MachRead} (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.lit l) st) :=
  satKE_conv_atom hst (by first | rfl | simp [convStep])

/-! ## 8. The OPEN arms, as named premises (§3.4 G5, G6, G11, G12, G17 user-let, G18, G20) -/

/-- **G5 OPEN** (`instStep`, FD:427-439): `instSite_args` per argument; `ConvKind` / `EqvSound` / `uniq` at each
argument let (`machLetIndex`); the new entry's `InstArgKinds` and `InstProv` (`instProv_push`). -/
def ArmG5 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {c : Name} {org : InstOrigin} {ks : List MixedGateBinder} {res : MixedGateBinder}
    {args : List Lean.Expr} {st : MachRead},
    CallPreKE HK senv p en (Call.inst env c org ks res args st) → ReadInv HK senv p st →
    SatK HK senv p h (instStep env c org ks res args st)

/-- **G6 OPEN** (`instSStep`, FD:464-493; its parameter fold G7 is CLOSED, `satKE_instSParamFold`). -/
def ArmG6 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {st : MachRead},
    CallPreKE HK senv p en (Call.instS env c ks ty args st) → ReadInv HK senv p st →
    SatK HK senv p h (instSStep senv env c ks ty args st)

/-- **G11 OPEN** (conv let, user value, FD:376-379): new entry `.val x` (`ConvKind` at `rootFloat v`, D5,
`LetSrcKinds`, `EqvSound`, `uniq`, new-let `LetKindOk`). -/
def ArmG11 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false →
    machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

/-- **G12 OPEN, conv** (conv let, loop, FD:368-369): the created entry `mv` at Δ entry `mixedGateBinderKind? ty`
(`n = 1 ∧ kinds[b] = k`; candidate `LoopLetSrcKinds`). -/
def ArmG12conv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = true →
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

/-- **G12 OPEN, chain** (chain let, loop, FD:517-518; the loop part of G17). -/
def ArmG12chain (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = true →
    SatK HK senv p h (chainStep senv env (.letE nm ty v b nd) st)

/-- **G17 user-let OPEN** (chain let, user value, FD:525-528; as G11). -/
def ArmG17user (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false →
    machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    SatK HK senv p h (chainStep senv env (.letE nm ty v b nd) st)

/-- **G18 OPEN** (loopBody let, FD:540-545: named / alias / plain push, new entry `.val x`). -/
def ArmG18 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {base : Nat} {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.loopBody base env (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    SatK HK senv p h (loopBodyStep base env (.letE nm ty v b nd) st)

/-- **G20 OPEN** (loopRoot, FD:562-594): the issued `loopBody` call's entry `.state base n` at the `lam` binder and the
shared probe's `.state b0 n` (FD:556; `ws`-equality ⇒ kind equality). -/
def ArmG20 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {e : Lean.Expr} {st : MachRead},
    CallPreKE HK senv p en (Call.loopRoot env e st) → ReadInv HK senv p st →
    SatK HK senv p h (loopRootStep senv env e st)

/-- **The open obligations of LK1 (table form), exactly.** Every other arm of `step` is plugged in below. -/
structure LK1Open (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop where
  g5 : ArmG5 HK senv p en
  g6 : ArmG6 HK senv p en
  g11 : ArmG11 HK senv p en
  g12conv : ArmG12conv HK senv p en
  g12chain : ArmG12chain HK senv p en
  g17user : ArmG17user HK senv p en
  g18 : ArmG18 HK senv p en
  g20 : ArmG20 HK senv p en

/-! ## 9. Dispatchers (closed arms plugged in; open arms from `LK1Open`) -/

/-- `convStep` on an application: the eight recogniser outcomes in FD order. -/
theorem conv_app_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.app f a) st) := by
  cases h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs with
  | some q =>
    obtain ⟨dom, α, init, x⟩ := q
    exact satKE_conv_bareReg HKL hG hE hpre hst h1
  | none =>
    cases h2 : machLoopRead? env d (.app f a) with
    | some i => exact satKE_conv_loopRead hst h1 h2
    | none =>
      cases h3 : machRunApp? (.app f a) with
      | some q =>
        obtain ⟨dom, αs, initsE, body⟩ := q
        exact satKE_conv_nestedCall hG hpre hst h1 h2 h3
      | none =>
        cases h4 : machInstCall? senv (.app f a) with
        | some q =>
          obtain ⟨c, ks, res, args⟩ := q
          exact satKE_conv_instCall hG hpre hst h1 h2 h3 h4
        | none =>
          cases h5 : machInstCallS? senv (.app f a) with
          | some q =>
            obtain ⟨c, ks, ty, args⟩ := q
            exact satKE_conv_instSCall hG hpre hst h1 h2 h3 h4 h5
          | none =>
            cases h6 : Sparkle.Compiler.MachMemory.memCall?
                (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) with
            | some q =>
              obtain ⟨combo, aw, dw, dom, ops⟩ := q
              exact satKE_conv_memCall HKL hG hpre hst h1 h2 h3 h4 h5 h6
            | none =>
              cases h7 : machReadV env d (.app f a) with
              | some i => exact satKE_conv_readV hst h1 h2 h3 h4 h5 h6 h7
              | none => exact satKE_conv_app_generic HKL hG hE hpre hst h1 h2 h3 h4 h5 h6 h7

/-- `convStep` on a `let` (FD:362-379): float G10, loop G12 (open), `.regs`/`.handle` G13, user value G11 (open). -/
theorem conv_letE_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (O : LK1Open HK senv p en) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st) := by
  by_cases hfl : ∃ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2
  · obtain ⟨n2, t2, v2, w, nd2, hf⟩ := hfl
    exact satKE_conv_letFloat hG hpre hst hf
  · have hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
        Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2 :=
      fun n2 t2 v2 w nd2 hf => hfl ⟨n2, t2, v2, w, nd2, hf⟩
    cases hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 with
    | true => exact O.g12conv hG hE hpre hst hnf hnl
    | false =>
      cases hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) with
      | some q => exact satKE_conv_letRegs hG hpre hst hnf hnl hq
      | none =>
        cases hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) with
        | some i => exact satKE_conv_letHandle hG hpre hst hnf hnl hq hi
        | none => exact O.g11 hG hE hpre hst hnf hnl hq hi

/-- `convStep`: all twelve `Expr` constructors. -/
theorem conv_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (convStep senv env d e st) := by
  cases e with
  | bvar j => exact satKE_conv_bvar hst
  | fvar x => exact satKE_conv_fvar hst
  | mvar m => exact satKE_conv_mvar hst
  | sort u => exact satKE_conv_sort hst
  | const c us => exact satKE_conv_const hst
  | app f a => exact conv_app_satKE HKL hG hE hpre hst
  | lam nm t b bi => exact satKE_conv_lam HKL hG hE hpre hst
  | forallE nm t b bi => exact satKE_conv_forallE HKL hG hE hpre hst
  | letE nm ty v b nd => exact conv_letE_satKE O hG hE hpre hst
  | lit l => exact satKE_conv_lit hst
  | mdata md x => exact satKE_conv_mdata
  | proj s i x => exact satKE_conv_proj

/-- `chainStep` on a `let` (FD:511-528): float, loop G12 (open), `.regs`/`.handle`, user value G17 (open). -/
theorem chain_letE_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (O : LK1Open HK senv p en) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.chain env (.letE nm ty v b nd) st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (chainStep senv env (.letE nm ty v b nd) st) := by
  by_cases hfl : ∃ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2
  · obtain ⟨n2, t2, v2, w, nd2, hf⟩ := hfl
    exact satKE_chain_letFloat hG rfl hpre hst hf
  · have hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
        Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2 :=
      fun n2 t2 v2 w nd2 hf => hfl ⟨n2, t2, v2, w, nd2, hf⟩
    cases hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 with
    | true => exact O.g12chain hG hE hpre hst hnf hnl
    | false =>
      cases hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) with
      | some q => exact satKE_chain_letRegs hG rfl hpre hst hnf hnl hq
      | none =>
        cases hi : machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) with
        | some i => exact satKE_chain_letHandle hG rfl hpre hst hnf hnl hq hi
        | none => exact O.g17user hG hE hpre hst hnf hnl hq hi

/-- `chainStep` (FD:497-529): `pure'` and `next` (G16, the closed batch-2/3 proofs, inlined after the split), `let`
(`chain_letE_satKE`), otherwise FAIL. -/
theorem chain_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (chainStep senv env e st) := by
  revert hpre
  unfold chainStep
  split
  · -- `pure'` (G16; body of `satKE_chain_pure`)
    intro hpre
    obtain ⟨Δ, hEnv, hR⟩ := hpre
    refine satK_bindO (satK_cConvE hG ⟨Δ, hEnv, ReadSub.appA hR⟩ hst) ?_
    rintro ⟨v', st1⟩ h1
    exact satK_okO h1
  · -- `next` (G16; body of `satKE_chain_next`)
    intro hpre
    obtain ⟨Δ, hEnv, hR⟩ := hpre
    refine satK_bind ?_
    intro r hr
    have hr' : ∀ a b, r = some (a, b) → ReadInv HK senv p b ∧ PhExt st b := by
      intro a b hrab
      subst hrab
      exact ⟨satK_cConvE hG ⟨Δ, hEnv, ReadSub.appA (ReadSub.appA (ReadSub.appF hR))⟩ hst (a, b) hr,
        cConv_phExt hE (a, b) hr⟩
    revert hr'
    split
    · intro hr'
      obtain ⟨h1, hx1⟩ := hr' _ _ rfl
      refine satK_ite2 (fun _ => ?_) (fun _ => satK_failO)
      refine satK_bindO (satK_cChainE hG ⟨_, envKindOkE_cons _ MachVal.unit (fun _ _ _ => trivial)
        (envKindOkE_ext HKL hEnv hx1), ReadSub.lamB (ReadSub.appA hR)⟩ h1) ?_
      rintro ⟨ws, v, st2⟩ h2
      exact satK_okO h2
    · intro _
      exact satK_failO
  · -- `let` (G17)
    intro hpre
    have key := chain_letE_satKE O hG hE hpre hst
    exact key
  · intro _
    exact satK_failO

/-- `loopBodyStep` (FD:539-549): `let` G18 (open), tail G19 (closed, `satKE_loopBody_tail`). -/
theorem loopBody_satKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {base : Nat} {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.loopBody base env e st)) (hst : ReadInv HK senv p st) :
    SatK HK senv p h (loopBodyStep base env e st) := by
  by_cases hl : ∃ (nm : Name) (ty v b : Lean.Expr) (nd : Bool), e = .letE nm ty v b nd
  · obtain ⟨nm, ty, v, b, nd, he⟩ := hl
    subst he
    exact O.g18 hG hE hpre hst
  · exact satKE_loopBody_tail HKL hG hE (fun nm ty v b nd he => hl ⟨nm, ty, v, b, nd, he⟩) hpre hst

/-! ## 10. LK1 SKELETON (table form, §3.4): fuel induction over `step` -/

/-- One step keeps `GoodKE`, given `GoodKE ∧ GoodE` of the table and the OPEN arms. -/
theorem step_goodKE {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) {h : Hs}
    (hG : GoodKE HK senv p en h) (hE : GoodE h) :
    GoodKE HK senv p en (fun c => (step senv c).run h) := by
  intro c hpre hst v hv
  cases c with
  | conv env d e st => exact conv_satKE HKL O hG hE hpre hst v hv
  | nested env dom αs initsE body st => exact satKE_nested HKL hG hE hpre hst v hv
  | inst env c org kinds res args st => exact O.g5 hG hE hpre hst v hv
  | instS env c kinds ty args st => exact O.g6 hG hE hpre hst v hv
  | chain env e st => exact chain_satKE HKL O hG hE hpre hst v hv
  | loopBody base env e st => exact loopBody_satKE HKL O hG hE hpre hst v hv
  | loopRoot env e st => exact O.g20 hG hE hpre hst v hv

/-- **LK1 skeleton**: `GoodKE` of the fuel reader at every fuel, FROM the eight open arms (`LK1Open`). CONDITIONAL:
not a completion claim; G21 / the run form are outside it. -/
theorem goodKE_readF_of_open {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) : ∀ n, GoodKE HK senv p en (readF senv n)
  | 0 => fun c _ _ v hv => by
    have hv' : (none : Option (RB c)) = some (some v) := hv
    cases hv'
  | n + 1 => step_goodKE HKL O (goodKE_readF_of_open HKL O n) (goodE_readF senv n)

end Tools.ShippingGen3ArgSupply4
