import Sparkle
import Sparkle.Compiler.Elab
import Tools.VedMemEntry
import Tools.VedSupplement

/-!
# Checks for the user-supplied lemma of one local condition (sparkle-ved-proof-supplement, `Tools/VedSupplement.lean`)

The condition: the causal side condition `hS` of the memory loop of `memQuantS` (`∀ t s₁ s₂, (∀ k ≤ t, s₁.val k = s₂.val k) →
(F s₁).val (t+1) = (F s₂).val (t+1)`, local context: `ins : Nat → String → Nat`), as `ved_loop_unfold_mem` meets it.
`set_option ved.mem.loopGate 1` makes the automation refuse it (the existing refusal, "more than the configured limit"); the option
`ved.mem.userLemma "<constant>"` then closes exactly that condition with an already proved theorem.

* (a) gate 1, no lemma: refused (existing path); gate 1 + `qCausal`: accepted, stored type `==` the statement, axioms std3, the final
  proof term contains `qCausal`, the generation ms and the kernel ms are recorded separately (`Tools.VedSupplement.lastRun`).
* (b) refused: a lemma of a different type (`qWrongType`), of another circuit (`qCausalOther`, same shape about another body), with `sorry`
  (matching type, `sorryAx`), with `native_decide` (matching type, `Lean.ofReduceBool`), one that leaves a hypothesis open
  (`qCausalHyp`, an unproved `h`), an unknown constant, a def; the declaration is not added in any of them.
* (c) the final theorem of the lemma run and of the automatic run (no lemma, default gate) have the SAME type (`==`, hence the same binder
  list and statement constant), the same registered contract, module and body.
-/

namespace Tests.Ved.VedSupplementCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.StateMacro
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedMemEntry

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

declare_signal_state QState
  | idx  : BitVec 5  := 0#5
  | busy : Bool      := false
  | last : BitVec 16 := 0#16

/-- the loop body of `memQuantS`, named so that the lemma can be stated about it -/
def qBody {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (state : Signal dom QState) : Signal dom QState :=
  let idx := QState.idx state
  let busy := QState.busy state
  let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
  let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
  let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
  let isNeg := signBit === 1#1
  let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
  let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
  let done := busy &&& (idx === 15#5)
  let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
  let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
  bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]

/-- the same body with another index step (`+ 2`): another circuit -/
def qBodyOther {dom : DomainConfig} (start writeEn : Signal dom Bool) (writeAddr : Signal dom (BitVec 4))
    (writeData : Signal dom (BitVec 16)) (state : Signal dom QState) : Signal dom QState :=
  let idx := QState.idx state
  let busy := QState.busy state
  let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
  let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
  let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
  let isNeg := signBit === 1#1
  let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
  let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
  let done := busy &&& (idx === 15#5)
  let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
  let idxNext := Signal.mux busy (idx + 2#5) (Signal.pure 0#5)
  bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]

/-- the design: `memQuant` of `VedMemCheck` -/
def memQuantS {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := QState.idx state
    let busy := QState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  QState.last state

/-- the same design under another name: the automatic path, the reference of (c) -/
def memQuantA {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := QState.idx state
    let busy := QState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  QState.last state

/-- the same design under a third name: the target of the refusals (no declaration is added by any of them) -/
def memQuantB {dom : DomainConfig} (start : Signal dom Bool) (writeEn : Signal dom Bool)
    (writeAddr : Signal dom (BitVec 4)) (writeData : Signal dom (BitVec 16)) : Signal dom (BitVec 16) :=
  let state := Signal.loop fun state =>
    let idx := QState.idx state
    let busy := QState.busy state
    let readAddr4 := idx.map (BitVec.extractLsb' 0 4 ·)
    let inputCoeff := Signal.memoryComboRead writeAddr writeData writeEn readAddr4
    let signBit := inputCoeff.map (BitVec.extractLsb' 15 1 ·)
    let isNeg := signBit === 1#1
    let result := Signal.mux isNeg (0#16 - inputCoeff) inputCoeff
    let outMemRead := Signal.memory readAddr4 result busy (Signal.pure 0#4)
    let done := busy &&& (idx === 15#5)
    let busyNext := Signal.mux done (Signal.pure false) (Signal.mux start (Signal.pure true) busy)
    let idxNext := Signal.mux busy (idx + 1#5) (Signal.pure 0#5)
    bundleAll! [Signal.register 0#5 idxNext, Signal.register false busyNext, Signal.register 0#16 outMemRead]
  QState.last state

/-- the body at the inputs `ins` (the names the generated script uses for the design's inputs) -/
def qF (ins : Nat → String → Nat) (s : Signal defaultDomain QState) : Signal defaultDomain QState :=
  qBody (PTy.bit.sig ins "_gen_start") (PTy.bit.sig ins "_gen_writeEn") ((PTy.bv 4).sig ins "_gen_writeAddr")
    ((PTy.bv 16).sig ins "_gen_writeData") s

def qFOther (ins : Nat → String → Nat) (s : Signal defaultDomain QState) : Signal defaultDomain QState :=
  qBodyOther (PTy.bit.sig ins "_gen_start") (PTy.bit.sig ins "_gen_writeEn") ((PTy.bv 4).sig ins "_gen_writeAddr")
    ((PTy.bv 16).sig ins "_gen_writeData") s

/-! ## The lemmas (proved with the memory loop's own tactic for the condition) -/

/-- the user's lemma: the causal side condition of the loop body `qF` -/
theorem qCausal : ∀ (ins : Nat → String → Nat) (t : Nat) (s₁ s₂ : Signal defaultDomain QState),
    (∀ k, k ≤ t → s₁.val k = s₂.val k) → (qF ins s₁).val (t + 1) = (qF ins s₂).val (t + 1) := by
  intro ins
  unfold qF qBody
  ved_causal [QState.idx, QState.busy, QState.last, PTy.sig]

/-- another circuit's lemma (its body steps the index by 2) -/
theorem qCausalOther : ∀ (ins : Nat → String → Nat) (t : Nat) (s₁ s₂ : Signal defaultDomain QState),
    (∀ k, k ≤ t → s₁.val k = s₂.val k) → (qFOther ins s₁).val (t + 1) = (qFOther ins s₂).val (t + 1) := by
  intro ins
  unfold qFOther qBodyOther
  ved_causal [QState.idx, QState.busy, QState.last, PTy.sig]

/-- a lemma of a different type (about the same body, the value at cycle `t` against itself) -/
theorem qWrongType : ∀ (ins : Nat → String → Nat) (t : Nat) (s₁ : Signal defaultDomain QState),
    (qF ins s₁).val t = (qF ins s₁).val t := fun _ _ _ => rfl

/-- the matching statement, proved by `sorry` -/
theorem qCausalSorry : ∀ (ins : Nat → String → Nat) (t : Nat) (s₁ s₂ : Signal defaultDomain QState),
    (∀ k, k ≤ t → s₁.val k = s₂.val k) → (qF ins s₁).val (t + 1) = (qF ins s₂).val (t + 1) := by
  sorry

/-- the matching statement, proved with the help of a `native_decide` fact -/
theorem qCausalNative : ∀ (ins : Nat → String → Nat) (t : Nat) (s₁ s₂ : Signal defaultDomain QState),
    (∀ k, k ≤ t → s₁.val k = s₂.val k) → (qF ins s₁).val (t + 1) = (qF ins s₂).val (t + 1) := by
  have _ : 2 + 2 = 4 := by native_decide
  exact qCausal

/-- the matching conclusion under an unproved hypothesis `h` (the match does not determine it) -/
theorem qCausalHyp : ∀ (ins : Nat → String → Nat) (h : 1 = 2) (t : Nat) (s₁ s₂ : Signal defaultDomain QState),
    (∀ k, k ≤ t → s₁.val k = s₂.val k) → (qF ins s₁).val (t + 1) = (qF ins s₂).val (t + 1) :=
  fun ins _ => qCausal ins

/-- a def, not a theorem -/
def qCausalDef : Nat := 0

/-! ## Running the entry as a function -/

/-- `#ved_u1_mem decl` under the options: `Except` the refusal text / the registered theorem's name -/
def runEntry (decl : Name) (gate : Option Nat) (lem : Option String) : TermElabM (Except String Name) := do
  let opts ← getOptions
  let opts := match gate with | some g => opts.insert `ved.mem.loopGate (.ofNat g) | none => opts
  let opts := match lem with | some l => opts.insert `ved.mem.userLemma (.ofString l) | none => opts
  -- each call is accounted from its own start (as a separate command would be); the limit itself is unchanged
  let hb ← IO.getNumHeartbeats
  withTheReader Core.Context (fun c => { c with initHeartbeats := hb }) <| withOptions (fun _ => opts) do
    try
      let (_, _, thm, _) ← vedMemEntryS decl
      return .ok thm
    catch e => return .error (← e.toMessageData.toString)

def has (s sub : String) : Bool := (s.splitOn sub).length > 1

def refusedWith (what : String) (decl : Name) (gate : Option Nat) (lem : Option String) (needle : String) : TermElabM Unit := do
  match ← runEntry decl gate lem with
  | .ok _ => throwError "{what}: accepted, expected a refusal"
  | .error msg =>
    unless has msg needle do throwError "{what}: refused, but not with `{needle}`:\n{msg.take 600}"
    if (← getEnv).contains (decl ++ `ved_mem) then throwError "{what}: refused, but the declaration was added"
    logInfo m!"{what}: refused ({needle})"

/-! ## (a) the open condition, closed by the lemma -/

/-- the stored theorem: type `==` the statement of the registered contract/module, axioms std3 -/
def storedOk (decl : Name) : TermElabM Unit := do
  let (stmt, _) ← specialiseDomain decl
  let thm := decl ++ `ved_mem
  let ti ← getConstInfo thm
  let expected := mkAppN (Lean.mkConst ``Tools.VedMem.MemStmt)
    #[Lean.mkConst (decl ++ `ved_contract), Lean.mkConst (decl ++ `ved_mod), stmt]
  unless ti.type == expected do throwError "{thm}: stored type differs from the statement"
  let axs ← collectAxioms thm
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless axs.all (std.contains ·) && std.all (axs.contains ·) do throwError "{thm}: axioms {axs}"
  logInfo m!"stored type == statement, axioms std3: {decl}"

/-- `x` with the declaration name `a` replaced by `b` in constants and string literals (the module name and the statement mention it) -/
def renameDecl (a b : Name) (e : Expr) : Expr :=
  let sub : String → String := fun s => (s.replace a.toString b.toString)
  e.replace fun
    | .const n us => if a.isPrefixOf n then some (.const (n.replacePrefix a b) us) else none
    | .lit (.strVal s) => some (.lit (.strVal (sub s)))
    | _ => none

/-- what (c) compares: the final theorem's type and the registered artifact, with the design's name replaced by `S` -/
def snapshot (decl : Name) : TermElabM (Expr × Expr × Expr × Expr) := do
  let n := fun x => do pure (renameDecl decl ``memQuantS ((← getConstInfo (decl ++ x)).value?.getD (Lean.mkConst ``True)))
  return (renameDecl decl ``memQuantS (← getConstInfo (decl ++ `ved_mem)).type, ← n `ved_mod, ← n `ved_contract, ← n `ved_body)

/-- the constant `c` is reached from the proof of `thm` through constants of this module (the proof's auxiliary lemmas included) -/
def reaches (thm c : Name) : TermElabM Bool := do
  let env ← getEnv
  let mine := fun (n : Name) => (`Tests.Ved.VedSupplementCheck).isPrefixOf n || (`_private.Tests.Ved.VedSupplementCheck).isPrefixOf n
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[thm]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v := match ci with | .thmInfo t => t.value | .defnInfo d => d.value | _ => Lean.mkConst ``True
    for u in v.getUsedConstants do
      if u == c then return true
      if mine u && !seen.contains u then todo := todo.push u
  return false

def partA : TermElabM Unit := do
  let say := fun (s : String) => do logInfo m!"SUPP {s} t={← IO.monoMsNow}"
  say "start"
  let decl := ``memQuantS
  Tools.VedSupplement.lastRun.set {}
  -- the automation alone, default budgets, on the same design under another name: accepted (the reference for (c))
  let .ok _ ← runEntry ``memQuantA none none | throwError "automatic path refused"
  storedOk ``memQuantA
  let ra ← Tools.VedSupplement.lastRun.get
  logInfo m!"automatic run (no lemma): generation {ra.genMs} ms, kernel {ra.kernelMs} ms, lemma applications {ra.applied.size}"
  unless ra.applied.isEmpty do throwError "the automatic path applied a lemma"
  let auto ← snapshot ``memQuantA
  say "auto done"
  -- (a) the condition left open: the automation refuses it
  refusedWith "gate 1, no lemma" decl (some 1) none "more than the configured limit"
  say "refusal done"
  -- closed by the lemma; the gate is not consulted for it
  Tools.VedSupplement.lastRun.set {}
  let thm ← match ← runEntry decl (some 1) (some "Tests.Ved.VedSupplementCheck.qCausal") with
    | .ok thm => pure thm
    | .error msg => throwError "lemma run refused: {msg.take 3000}"
  say "lemma run done"
  storedOk decl
  let r ← Tools.VedSupplement.lastRun.get
  unless r.applied.size == 2 do throwError "the lemma was applied {r.applied.size} times, expected 2 (base case and step)"
  let some ti := (← getEnv).find? thm | throwError "no theorem"
  unless ← reaches thm ``qCausal do throwError "the final proof does not use qCausal"
  logInfo m!"lemma run: generation {r.genMs} ms, kernel {r.kernelMs} ms, match {r.applied.map (·.2)} ms"
  -- (c) same final theorem and artifact as the automatic path
  let user ← snapshot decl
  let autoTy := auto
  unless user.1 == auto.1 do throwError "final theorem type differs from the automatic one"
  unless user.2.1 == auto.2.1 && user.2.2.1 == auto.2.2.1 && user.2.2.2 == auto.2.2.2 do
    throwError "registered artifact differs from the automatic one"
  logInfo m!"(c) final theorem type, module, contract and body identical to the automatic path"

run_cmd liftTermElabM partA

/-! ## (b) refusals -/

def partB : TermElabM Unit := do
  let decl := ``memQuantB
  let L := fun (n : String) => some s!"Tests.Ved.VedSupplementCheck.{n}"
  refusedWith "wrong-type lemma" decl (some 1) (L "qWrongType") "does not match the goal"
  refusedWith "lemma of another circuit" decl (some 1) (L "qCausalOther") "does not match the goal"
  refusedWith "lemma with sorry (matching type)" decl (some 1) (L "qCausalSorry") "sorryAx"
  refusedWith "lemma with native_decide (matching type)" decl (some 1) (L "qCausalNative") "native_decide"
  refusedWith "lemma with an unproved hypothesis" decl (some 1) (L "qCausalHyp") "leaves a binder undetermined"
  refusedWith "unknown constant" decl (some 1) (L "qNoSuchLemma") "unknown constant"
  refusedWith "a def" decl (some 1) (L "qCausalDef") "not a theorem"
  refusedWith "no lemma, gate 1 (existing refusal)" decl (some 1) none "more than the configured limit"
  -- a refused lemma is not retried by the automation: even without the gate the wrong lemma refuses
  refusedWith "wrong-type lemma, gate off" decl none (L "qWrongType") "does not match the goal"

run_cmd liftTermElabM partB
