import Tools.ShippingGen2SrcPkg
import Tools.ShippingMachineSeqLinkedR
import Tools.ShippingServedRealATrace
import Tools.ShippingQuadCalls
set_option autoImplicit false

/-! # Pkg.comb step 1: the slotless, call-free package (scripts/gen2/PKG_COMB_FREEZE.md §2-§3; approved for step 1)

ADDITIVE: no existing file is changed (no `Pkg` / Defs edit in this step).

* `CombFacts`: the generator's refl checks of a slotless declaration (`machine_ok`, `machine_body`, `machine_inits`,
  `machine_next`, `machine_result`). It does NOT require `slots = []` or `insts = []`; nothing here assumes them.
  `hres` is the source ↔ IR tie: `src` is the declaration's elaborated observations (`machineSource`), not the IR meaning.
* `CombPkg`: the package; `extS`/`extBS` are the identity on the inputs, `lsrc` the `let` observations at the constant
  state (`letObsComb`, Tools/ShippingMachineSeqLinked.lean:138), not `[]`.
* `machine_traceL_of_comb_callsRA_ranA`: `machine_traceL_of_comb_callsRA_ran` (Tools/ShippingMachineSeqLinkedR.lean:195)
  on the A-boundary: the same stream witness, with `machine_trace_lets_of_streamBRA_ranA`
  (Tools/ShippingServedRealATrace.lean:36) in place of `_streamBRA_ran`; it never uses `MachineRan`/`ServedReal`.
* `combTrace`: the wrapper (as `genTraceL`, Tools/ShippingGen2Loop.lean:212, and `genTrace`,
  Tools/ShippingQuadComposed.lean:156), at the SAME `ran`.
* `CombPkg.lsrc_hl`, `CombPkg.src_length`: the per-package facts `Pkg.lsrc_hl` / `Pkg.src_length` will use. -/
namespace Tools.ShippingGen2
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX Tools.ShippingServedRealA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineCausal
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`CombFacts`**: the generated facts of a slotless declaration (FREEZE §2), the premises of
`machine_traceL_of_comb_callsRA_ran` at `ext := fun _ _ bits => bits`, `extB := fun _ bools _ => bools` (beta-reduced). -/
structure CombFacts (d : MachineData) {ι : Type} (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      List (Nat → Nat)) : Prop where
  ok : d.ok = true
  hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
            (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  hinit : d.initOk inits = true
  hnext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (t : Nat),
    inits = evalTerms (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos j) w) d.nexts
  hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (t : Nat),
    (src i bools bits).map (fun g => g t) =
      d.outs.map fun o => enc o.1 (eval (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).b (d.bpos k))
        (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t inits).v (d.vpos k) w) o.2)

set_option maxHeartbeats 2000000 in
/-- **`machine_traceL_of_comb_callsRA_ranA`** (FREEZE §3): `machine_traceL_of_comb_callsRA_ran` on the A-boundary,
the same witness `⟨fun _ => inits, rfl, hnext, hres, …⟩`; no causality premise (`ext` reads no state signal). -/
theorem machine_traceL_of_comb_callsRA_ranA (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {n : Nat}
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named))
    {declName : Name} (d : MachineData) {ι : Type} (dom : ι → DomainConfig) (inits : HList (tys d.ss))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (hF : CombFacts d dom inits src)
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : MachineRunJQC O mctx cctx n declName d.shape m design) :
    MachineTraceLBX (ServedRealA O declName d.shape m design) declName d m design dom src
      (fun _ _ bits => bits) (fun _ bools _ => bools)
      (letObsComb d dom inits (fun _ _ bits => bits) (fun _ bools _ => bools)) := by
  refine Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_ranA O hB hA htr d dom inits src
    (letObsComb d dom inits (fun _ _ bits => bits) (fun _ bools _ => bools)) hF.ok hF.hbody hF.hinit
    (fun _ _ bits => bits) (fun _ bools _ => bools) ?_ ran
  intro i bools bits
  refine ⟨fun _ => inits, rfl, fun t => hF.hnext i bools bits t, hF.hres i bools bits, ?_⟩
  intro j q g l hg hl
  simp only [letObsComb, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
  rw [← hg]

/-- **The slotless, call-free package** (FREEZE §2). -/
structure CombPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  inits : HList (tys d.ss)
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  facts : CombFacts d dom inits src

variable {ι : Type} {dom : ι → DomainConfig}

/-- The package's input wiring: the identity (no state signal is read). -/
def CombPkg.extS (_p : CombPkg ι dom) :=
  fun (i : ι) (_ : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bits
def CombPkg.extBS (_p : CombPkg ι dom) :=
  fun (i : ι) (bools : Nat → Signal (dom i) Bool) (_ : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bools
/-- The package's `let` observations (at the constant state `inits`). -/
noncomputable def CombPkg.lsrc (p : CombPkg ι dom) :=
  letObsComb p.d dom p.inits (fun _ _ bits => bits) (fun _ bools _ => bools)

/-- **`CombPkg.lsrc_hl`**: the `Pkg.lsrc_hl` shape (Tools/ShippingGen2Pkg.lean:91), proof as `letObsLoop_hl`. -/
theorem CombPkg.lsrc_hl (p : CombPkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (a : Nat) (l : Σ s : SType, Term s), p.d.ls[a]? = some l →
      ∃ v, (p.lsrc i bools bits)[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width := by
  intro a l hl
  unfold CombPkg.lsrc letObsComb
  rw [List.getElem?_map, hl]
  exact ⟨_, rfl, fun τ => Tools.ShippingQuadCalls.enc_lt l.1 _⟩

/-- **`CombPkg.src_length`**: one source observation per data output term (from `hres` at `t = 0`). -/
theorem CombPkg.src_length (p : CombPkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (p.src i bools bits).length = p.d.outs.length := by
  have hr := congrArg List.length (p.facts.hres i bools bits 0)
  simp only [List.length_map] at hr
  exact hr

/-- **`combTrace`** (exact A-boundary form, as `genTraceL` / `genTrace`), at the same `ran`. -/
theorem combTrace (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (p : CombPkg ι dom) {D₀ : Nat} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (ran : MachineRunJQC O mctx cctx (D₀ + 1) p.decl p.d.shape m design) :
    MachineTraceLBX (ServedRealA O p.decl p.d.shape m design) p.decl p.d m design dom p.src p.extS p.extBS p.lsrc := by
  exact machine_traceL_of_comb_callsRA_ranA O (Tools.ShippingChildComposeC.bodyStepC_of_tele O T) hA (n := D₀ + 1)
    (Tools.ShippingChildRunAMain.htr_of_tele O hA T D₀) (declName := p.decl) p.d dom p.inits p.src p.facts
    (m := m) (design := design) ran

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.machine_traceL_of_comb_callsRA_ranA
#print axioms Tools.ShippingGen2.combTrace
