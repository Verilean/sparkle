import Tools.ShippingGen5ReadKinds
import Tools.ShippingGen5T1ND
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT after the R1 edit (single-constant forbid controls). Previous tree: clean build rkav-4d5b7874 exit 0 (751 jobs).

/-! # DG-READKINDS checks (Tools/ShippingGen5ReadKinds.lean; scripts/gen5/DG_READKINDS_FREEZE.md rev2 3f79600f)

1. TYPE: each lemma of freeze §2 against an independently written `Exp…` statement (`isDefEq` through the
   `Tests.Gen3.ExpectedType` telescope comparison); `RootFacts` by its constructor telescope.
2. MUTANT: changed statements that the same comparison must reject. These are rejections by signature / defeq of a
   changed statement, NOT semantic counterexamples.
3. REACH: closure over explicit bodies. Must reach `readN_sound` (U3) / `readTerm2_quote` (U1 at k = 0) /
   `kindsCfg_complete'` (U4); must not reach a `T1Hyp` / `T1HypND` field, `Laws`, or `Lean.Expr.equal` / `eqv`.
   Controls: detector fixtures that do reach them, and an unrelated theorem that does not.
4. AXIOMS: only propext / Classical.choice / Quot.sound.

Directions kept apart (freeze §2.4): U3 `machine_wf_of_readN` `hw : d.vwL = widV (kindsOf d)` takes WF over `cfg` to
`d.packed.WF d.kb d.kv d.vw`; U4 `packed_wf_cfg` / `readTot_of_quote_body` use the same list equation the other way.
`hdom` of U3 (`∀ x, isDom x = true → x = d.dom`, soundness) is a different premise from U4's
(`isDom d.dom = true`, completeness). Each has a mutant that swaps them.
`RootFacts` is checked as a TYPE only; it is not a producer and is not counted as supply. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.ReadKindsFixture
theorem badDec : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.dec
theorem badNDCases : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.casesOn.{0}
theorem badEqual : True := (fun _ => trivial) @Lean.Expr.equal
theorem unrelated : True := trivial
end Tests.Gen5.ReadKindsFixture
namespace Tests.Gen5.ReadKindsFixtureOther
/-- a helper in ANOTHER namespace that reaches a forbidden constant only through a fixture theorem -/
theorem viaHelper : True := Tests.Gen5.ReadKindsFixture.badEqual
theorem viaHelper2 : True := viaHelper
theorem cleanHelper : True := Tests.Gen5.ReadKindsFixture.unrelated
end Tests.Gen5.ReadKindsFixtureOther

namespace Tests.Gen5.ReadKindsCheck
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingReaderTerm Tools.ShippingReaderInputs
open Tools.ShippingReaderNodes2 Tools.ShippingReaderApp Tools.ShippingReaderComplete
open Tools.ShippingReaderComplete2 Tools.ShippingReaderKinds Tools.ShippingReaderMachine
open Tools.ShippingMachineAuto Tools.ShippingGen5ReadKinds Tools.ShippingMuxTypeSoundness
open Tests.Gen3.ExpectedType
open Tools.ShippingMixedSourceBridge (inputExpr)

/-! ## 1. Expected types -/

def ExpReadNQuote : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg),
    ∀ {s : SType} (t : Term s) (k : Nat), liftDepth t ≤ k → t.WF cfg.kb cfg.kv cfg.vw →
      readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩

def ExpAppBool : Prop :=
  ∀ {cfg : Cfg}, ∀ (hd : cfg.isDom cfg.dom = true) (op : SignalBoolBinKind)
    {a b : Term .bool} {ra rb : Option AnyTerm} (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩),
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBoolBodyE op)) ra rb = some ⟨.bool, .appBool op a b⟩

def ExpAppBool2 : Prop :=
  ∀ {cfg : Cfg}, ∀ (hd : cfg.isDom cfg.dom = true) (f : AppBool2)
    {a b : Term .bool} {ra rb : Option AnyTerm} (ha : ra = some ⟨.bool, a⟩) (hb : rb = some ⟨.bool, b⟩),
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (.const ``Bool []) (.const ``Bool [])
      (mapHeadE cfg.dom (.const ``Bool []) (appBool2BodyE f)) ra rb = some ⟨.bool, .appBool2 f a b⟩

def ExpAppCompare : Prop :=
  ∀ {cfg : Cfg}, ∀ (hd : cfg.isDom cfg.dom = true) (op : SignalCompareKind) {w : Nat}
    {a b : Term (.bits w)} {ra rb : Option AnyTerm} (ha : ra = some ⟨.bits w, a⟩) (hb : rb = some ⟨.bits w, b⟩),
    readAp cfg ``Sparkle.Core.Signal.Signal.ap [.zero] cfg.dom (bitVecE w) (.const ``Bool [])
      (mapHeadE cfg.dom (bitVecE w) (appCompareBodyE op w)) ra rb = some ⟨.bool, .appCompare op a b⟩

def ExpReadNExprQuote : Prop :=
  ∀ (dom : Lean.Expr) (ks : List MixedGateBinder) {s : SType} (t : Term s) (k : Nat)
    (hk : liftDepth t ≤ k)
    (hw : t.WF (posB 0 ks).length (posV 0 ks).length (fun j => (widV ks).getD j 0)),
    readN (kindsCfg dom (isExpr dom) ks) k
      (quote dom (fun j => inputExpr ks.length ((posB 0 ks).getD j 0))
        (fun j => inputExpr ks.length ((posV 0 ks).getD j 0)) t) = some ⟨s, t⟩

def ExpQuoteInjective : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s) (t' : Term s')
    (hw : t.WF cfg.kb cfg.kv cfg.vw) (hw' : t'.WF cfg.kb cfg.kv cfg.vw)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t'),
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩

def ExpReadTotQuote : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg) {s : SType} (t : Term s) (hw : t.WF cfg.kb cfg.kv cfg.vw),
    readTot cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩

def ExpMono : Prop :=
  ∀ {cfg : Cfg} (hs : cfg.Sound) (hc : Complete cfg) {s : SType} (t : Term s)
    (hw : t.WF cfg.kb cfg.kv cfg.vw) {k : Nat} (r : AnyTerm)
    (hr : readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some r)
    {k' : Nat} (hk' : liftDepth t ≤ k'), readN cfg k' (quote cfg.dom cfg.bools cfg.bits t) = some r

def ExpBodyN : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)),
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

def ExpWfN : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)),
    d.packed.WF d.kb d.kv d.vw

def ExpQuoteArgs : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)),
    (kindsCfg d.dom isDom (kindsOf d)).bools = (fun j => inputExpr d.shape.binders.length (d.bpos j)) ∧
    (kindsCfg d.dom isDom (kindsOf d)).bits = (fun j => inputExpr d.shape.binders.length (d.vpos j))

def ExpPackedWf : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d)) (hwf : d.packed.WF d.kb d.kv d.vw),
    d.packed.WF (kindsCfg d.dom isDom (kindsOf d)).kb (kindsCfg d.dom isDom (kindsOf d)).kv
      (kindsCfg d.dom isDom (kindsOf d)).vw

def ExpReadTotBody : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : isDom d.dom = true)
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d)) (hwf : d.packed.WF d.kb d.kv d.vw),
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)

def ExpApNone : Prop :=
  ∀ {cfg : Cfg} (c : Lean.Name) (hc : c = ``Sparkle.Core.Signal.Signal.ap)
    (ls : List Lean.Level) (args : List Arg), readNode2 cfg c ls args = none

def ExpDepthLe : Prop :=
  ∀ {cfg : Cfg} {s : SType} (t : Term s),
    liftDepth t ≤ exprSize (quote cfg.dom cfg.bools cfg.bits t)

/-- `RootFacts`, written independently. -/
structure ExpRootFacts (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder))
    (entryBody₀ entryBody : Lean.Expr) : Prop where
  pack  : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
  float : entryBody = Sparkle.Compiler.MachRawSurface.rootFloat entryBody₀

structure MutRootFactsArg (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder))
    (entryBody₀ entryBody : Lean.Expr) : Prop where
  pack  : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, entryBody₀)
  float : entryBody = Sparkle.Compiler.MachRawSurface.rootFloat entryV

/-- Constructor telescope comparison (names, order, binder info, types at reducible transparency). -/
def structPair (a b : Name) : MetaM Nat := do
  let env ← getEnv
  let some (.inductInfo i1) := env.find? a | throwError "no {a}"
  let some (.inductInfo i2) := env.find? b | throwError "no {b}"
  unless i1.numParams == i2.numParams do throwError "RK STRUCT FAILED: numParams"
  let c1 ← getConstInfo (a ++ `mk)
  let c2 ← getConstInfo (b ++ `mk)
  forallTelescope c1.type fun xs _ => do
    let ps := xs[:i1.numParams].toArray
    let mut t2 ← instantiateForall c2.type ps
    let mut j : Nat := 0
    for x in xs[i1.numParams:].toArray do
      let ld ← x.fvarId!.getDecl
      match t2 with
      | .forallE n ty bd bi =>
        unless n == ld.userName do throwError "RK STRUCT FAILED: field {j}: {n} ≠ {ld.userName}"
        unless bi == ld.binderInfo do throwError "RK STRUCT FAILED: binderInfo of {n}"
        unless ← withReducible (isDefEq ty ld.type) do throwError "RK STRUCT FAILED: type of {n}"
        t2 := bd.instantiate1 x
        j := j + 1
      | _ => throwError "RK STRUCT FAILED: {b}.mk has fewer fields (at {ld.userName})"
    if t2.isForall then throwError "RK STRUCT FAILED: {b}.mk has an EXTRA field"
    return j

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``readN_quote ``ExpReadNQuote
  checkExpected ``readAp_appBool_eval ``ExpAppBool
  checkExpected ``readAp_appBool2_eval ``ExpAppBool2
  checkExpected ``readAp_appCompare_eval ``ExpAppCompare
  checkExpected ``readN_expr_quote ``ExpReadNExprQuote
  checkExpected ``Tools.ShippingGen5ReadKinds.quote_injective ``ExpQuoteInjective
  checkExpected ``readTot_quote ``ExpReadTotQuote
  checkExpected ``readN_mono_on_quotes ``ExpMono
  checkExpected ``machine_body_of_readN ``ExpBodyN
  checkExpected ``machine_wf_of_readN ``ExpWfN
  checkExpected ``kindsCfg_quote_args ``ExpQuoteArgs
  checkExpected ``packed_wf_cfg ``ExpPackedWf
  checkExpected ``readTot_of_quote_body ``ExpReadTotBody
  checkExpected ``readNode2_ap_none ``ExpApNone
  checkExpected ``liftDepth_le_exprSize ``ExpDepthLe
  let j ← structPair ``RootFacts ``ExpRootFacts
  logInfo m!"RK STRUCT OK RootFacts: {j} fields = ExpRootFacts (names, order, binderInfo, types), no extra field (a TYPE only, not a producer)"

/-! ## 2. Mutants (signature / defeq rejections, not semantic counterexamples) -/

/-! Each mutant keeps every binder name and binder info of the expected statement and changes ONE point, so the
rejection is at the changed point (not at a spurious name difference). -/

/-- no level bound -/
def MutQuoteNoBound : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg),
    ∀ {s : SType} (t : Term s) (k : Nat), True → t.WF cfg.kb cfg.kv cfg.vw →
      readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩

/-- strict bound -/
def MutQuoteStrict : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg),
    ∀ {s : SType} (t : Term s) (k : Nat), liftDepth t < k → t.WF cfg.kb cfg.kv cfg.vw →
      readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩

/-- the eighteen-kind reader (`readTerm2`) in place of `readN cfg k` -/
def MutQuoteTerm2 : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg),
    ∀ {s : SType} (t : Term s) (k : Nat), liftDepth t ≤ k → t.WF cfg.kb cfg.kv cfg.vw →
      readTerm2 cfg (quote cfg.dom cfg.bools cfg.bits t) = some ⟨s, t⟩

/-- injectivity: second WF premise replaced by `True` -/
def MutInjNoWf : Prop :=
  ∀ {cfg : Cfg} (hc : Complete cfg) {s s' : SType} (t : Term s) (t' : Term s')
    (hw : t.WF cfg.kb cfg.kv cfg.vw) (hw' : True)
    (h : quote cfg.dom cfg.bools cfg.bits t = quote cfg.dom cfg.bools cfg.bits t'),
    (⟨s, t⟩ : AnyTerm) = ⟨s', t'⟩

/-- monotonicity read at a lower level `k' < k` -/
def MutMonoLower : Prop :=
  ∀ {cfg : Cfg} (hs : cfg.Sound) (hc : Complete cfg) {s : SType} (t : Term s)
    (hw : t.WF cfg.kb cfg.kv cfg.vw) {k : Nat} (r : AnyTerm)
    (hr : readN cfg k (quote cfg.dom cfg.bools cfg.bits t) = some r)
    {k' : Nat} (hk' : k' < k), readN cfg k' (quote cfg.dom cfg.bools cfg.bits t) = some r

/-- U3 body lemma stated for the eleven-kind reader `readTerm` (level dropped) -/
def MutBodyReadTerm : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : ∀ x, isDom x = true → x = d.dom) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hread : readTerm (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)),
    d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed

/-- U4 without `hq` (hq replaced by `True`: this would be the coverage statement the freeze §3 says is not supplied) -/
def MutReadTotNoHq : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : isDom d.dom = true)
    (hq : True)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d)) (hwf : d.packed.WF d.kb d.kv d.vw),
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)

/-- U4 with the width transport `hw` replaced by `True` -/
def MutReadTotNoHw : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : isDom d.dom = true)
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : True) (hwf : d.packed.WF d.kb d.kv d.vw),
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)

/-- `packed_wf_cfg` with `hw` replaced by `True` -/
def MutPackedWfNoHw : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : True) (hwf : d.packed.WF d.kb d.kv d.vw),
    d.packed.WF (kindsCfg d.dom isDom (kindsOf d)).kb (kindsCfg d.dom isDom (kindsOf d)).kv
      (kindsCfg d.dom isDom (kindsOf d)).vw

/-- U4 with U3's soundness-direction `hdom` -/
def MutReadTotSoundDom : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : ∀ x, isDom x = true → x = d.dom)
    (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d)) (hwf : d.packed.WF d.kb d.kv d.vw),
    readTot (kindsCfg d.dom isDom (kindsOf d)) d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)

/-- U3 WF lemma with U4's completeness-direction `hdom` -/
def MutWfNCompleteDom : Prop :=
  ∀ (d : MachineData) (isDom : Lean.Expr → Bool) (hdom : isDom d.dom = true) (k : Nat)
    (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d))
    (hw : d.vwL = widV (kindsOf d))
    (hread : readN (kindsCfg d.dom isDom (kindsOf d)) k d.shape.body = some (⟨_, d.packed⟩ : AnyTerm)),
    d.packed.WF d.kb d.kv d.vw

/-- U1 ap-none lemma with the head `Signal.pure` (hypothesis changed to a different constant) -/
def MutApNonePure : Prop :=
  ∀ {cfg : Cfg} (c : Lean.Name) (hc : c = ``Sparkle.Core.Signal.Signal.pure)
    (ls : List Lean.Level) (args : List Arg), readNode2 cfg c ls args = none

run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutant ``readN_quote ``MutQuoteNoBound
  checkMutant ``readN_quote ``MutQuoteStrict
  checkMutant ``readN_quote ``MutQuoteTerm2
  checkMutant ``readNode2_ap_none ``MutApNonePure
  checkMutant ``Tools.ShippingGen5ReadKinds.quote_injective ``MutInjNoWf
  checkMutant ``readN_mono_on_quotes ``MutMonoLower
  checkMutant ``machine_body_of_readN ``MutBodyReadTerm
  checkMutant ``readTot_of_quote_body ``MutReadTotNoHq
  checkMutant ``readTot_of_quote_body ``MutReadTotNoHw
  checkMutant ``packed_wf_cfg ``MutPackedWfNoHw
  checkMutant ``readTot_of_quote_body ``MutReadTotSoundDom
  checkMutant ``machine_wf_of_readN ``MutWfNCompleteDom
  let acc ← try
      let _ ← structPair ``RootFacts ``MutRootFactsArg
      pure true
    catch e => do
      logInfo m!"RK STRUCT NEGATIVE REJECTED MutRootFactsArg: {e.toMessageData}"
      pure false
  if acc then throwError "RK STRUCT NEGATIVE ACCEPTED: MutRootFactsArg"

/-! ## 3. Closure audit -/

def forbidConsts : List Name :=
  [``Tools.ShippingGen2.T1Hyp.rec, ``Tools.ShippingGen2.T1Hyp.casesOn, ``Tools.ShippingGen2.T1Hyp.recOn,
   ``Tools.ShippingGen2.T1HypND.rec, ``Tools.ShippingGen2.T1HypND.casesOn, ``Tools.ShippingGen2.T1HypND.recOn,
   ``Tools.ShippingGen2.Laws, ``Lean.Expr.equal, ``Lean.Expr.eqv] ++
  (["pkg", "defines", "closes", "dec", "closed"].map fun f => (``Tools.ShippingGen2.T1Hyp).str f) ++
  (["pkg", "defines", "closes", "closed"].map fun f => (``Tools.ShippingGen2.T1HypND).str f)

def badProj (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => s == ``Tools.ShippingGen2.T1Hyp || s == ``Tools.ShippingGen2.T1HypND ||
        s == ``Tools.ShippingGen2.Laws
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Nat := 0
  opaqueNames : Array Name := #[]
  unknown : Array Name := #[]
  noBodyNames : Array Name := #[]

def reach (root : Name) (cap : Nat := 3000000) (forbid : List Name := forbidConsts) (rawProj : Bool := true) :
    MetaM AReach := do
  let env ← getEnv
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "RK AUDIT INCOMPLETE at {root}"
    let some ci := env.find? c | do
      out := { out with unknown := out.unknown.push c }
      continue
    let body := body? ci
    if body.isNone then out := { out with noBody := out.noBody + 1, noBodyNames := out.noBodyNames.push c }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques + 1, opaqueNames := out.opaqueNames.push c }
    if rawProj && (badProj ci.type || (body.map badProj).getD false) then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj ``Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "RK AUDIT FAILED: raw T1Hyp proj missed"
  unless badProj (.proj ``Tools.ShippingGen2.T1HypND 1 (.bvar 0)) do throwError "RK AUDIT FAILED: raw T1HypND proj missed"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "RK AUDIT FAILED: unrelated raw proj flagged"
  logInfo "RK CONTROL rawProj: T1Hyp/T1HypND flagged, Prod not flagged"
  let F := `Tests.Gen5.ReadKindsFixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badNDCases, true), (F ++ `badEqual, true),
      (`Tests.Gen5.ReadKindsFixtureOther.viaHelper, true),
      (`Tests.Gen5.ReadKindsFixtureOther.viaHelper2, true),
      (F ++ `unrelated, false), (`Tests.Gen5.ReadKindsFixtureOther.cleanHelper, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "RK AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "RK AUDIT FAILED: detector flags {c}"
    logInfo m!"RK CONTROL {c}: {toString r.hit}"
  -- R1: each fixture against ONLY its intended constant (raw-proj check off, forbid set = that one constant).
  -- With the full list both fixtures are also hit via `Laws`; this isolates the intended detection path.
  for (c, one) in [(F ++ `badDec, ``Tools.ShippingGen2.T1Hyp.dec),
      (F ++ `badNDCases, ``Tools.ShippingGen2.T1HypND.casesOn), (F ++ `badEqual, ``Lean.Expr.equal)] do
    let r ← reach c (forbid := [one]) (rawProj := false)
    match r.hit with
    | none => throwError "RK AUDIT FAILED: single-constant forbid {one} misses {c}"
    | some p =>
      unless p.getLast? == some one do throwError "RK AUDIT FAILED: {c} hit via {p}, not {one}"
      logInfo m!"RK CONTROL-SINGLE {c} forbid only {one}: hit path {p}"
  -- must reach (positive controls of the audit: the proofs really go through these)
  for (c, req) in [(``readN_quote, [``readTerm2_quote, ``readAp_appBool_eval, ``readAp_appCompare_eval,
        ``readNode2_ap_none]),
      (``readN_expr_quote, [``readN_quote, ``kindsCfg_complete']),
      (``Tools.ShippingGen5ReadKinds.quote_injective, [``readN_quote]),
      (``readTot_quote, [``readN_quote, ``liftDepth_le_exprSize]),
      (``readN_mono_on_quotes, [``readN_sound, ``readN_quote, ``Tools.ShippingGen5ReadKinds.quote_injective]),
      (``machine_body_of_readN, [``readN_sound, ``kindsCfg_sound]),
      (``machine_wf_of_readN, [``readN_sound, ``kindsCfg_sound]),
      (``readTot_of_quote_body, [``kindsCfg_complete', ``readTot_quote, ``packed_wf_cfg,
        ``kindsCfg_quote_args])] do
    let r ← reach c
    if let some p := r.hit then throwError "RK AUDIT FAILED {c}: forbidden use via {p}"
    for t in req do
      unless r.seen.contains t do throwError "RK AUDIT FAILED {c}: {t} not reached"
    logInfo m!"RK REACH {c}: no T1Hyp / T1HypND (named, raw proj, recursor) / Laws / Expr.equal / Expr.eqv; reaches {req} (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques}, unknown {r.unknown.size})"
    -- never a silent success: every constant whose body is not read is listed
    logInfo m!"RK REACH-UNREAD {c}: unknown constants {r.unknown}; opaque (value read, listed) {r.opaqueNames}; no value (axiom/inductive/ctor/rec/quot/opaque-less; type only) count {r.noBodyNames.size}"
    if !r.unknown.isEmpty then throwError "RK AUDIT FAILED {c}: unknown constants in the closure {r.unknown}"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``readN_quote, ``readAp_appBool_eval, ``readAp_appBool2_eval, ``readAp_appCompare_eval,
      ``readNode2_ap_none, ``core2_of_liftDepth_zero, ``liftDepth_le_exprSize,
      ``readN_expr_quote, ``Tools.ShippingGen5ReadKinds.quote_injective, ``readTot_quote, ``readN_mono_on_quotes,
      ``machine_body_of_readN, ``machine_wf_of_readN, ``kindsCfg_quote_args, ``packed_wf_cfg,
      ``readTot_of_quote_body, ``boolOp?_self, ``bool2Op?_self, ``cmpOp?_self] do
    checkAxioms n

/-! ## 5. Concrete instances (positive controls; not a substitute for the theorems)

`readTot` on the quotation of closed lift terms (depth 1, 2 through first operands) by `decide` on `isSome`/`isNone` of the closed `Expr` reading
(kernel evaluation, no `native_decide`; `Term` has no `DecidableEq`, so the value itself is not compared), and one negative control: `readN cfg 0` returns `none` on a lift. -/

def dom0 : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def cfg0 : Cfg := kindsCfg dom0 (isExpr dom0) []
def t1 : Term .bool := .appBool .band (.boolLit true) (.boolLit false)
def t2 : Term .bool := .appBool2 .nor t1 (.boolLit true)
def t4 : Term .bool := .appCompare .ule (.bitsLit 8 3) (.bitsLit 8 200)

theorem inst_t1 : (readTot cfg0 (quote cfg0.dom cfg0.bools cfg0.bits t1)).isSome = true := by decide
theorem inst_t2 : (readTot cfg0 (quote cfg0.dom cfg0.bools cfg0.bits t2)).isSome = true := by decide
theorem inst_t4 : (readTot cfg0 (quote cfg0.dom cfg0.bools cfg0.bits t4)).isSome = true := by decide
theorem neg_t1_level0 : (readN cfg0 0 (quote cfg0.dom cfg0.bools cfg0.bits t1)).isNone = true := by decide
theorem neg_t2_level1 : (readN cfg0 1 (quote cfg0.dom cfg0.bools cfg0.bits t2)).isNone = true := by decide

end Tests.Gen5.ReadKindsCheck
