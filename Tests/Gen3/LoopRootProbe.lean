import Tools.ShippingReaderFuelDriver           -- machineShapeF / driveShape / defaultRounds / resClass, shapeW, readF
import Tests.Compiler.ShippingMachineLoopTest     -- counterLoop, accLoop, wholeLoop, wholeToggle, divQ, loopPair (+ IP bottleneck / divider)
import Tests.Compiler.ShippingMachineSeqLoopTest  -- toggleL (imports ShippingMachineFuseTest: outer, siblings, withMemory)
import IP.Video.H264.QuantSynth                   -- quantModule (Tests/Gen2/QuantEndpoint.lean)
set_option autoImplicit false
-- WRITTEN, NOT BUILT (batch 4; no lake/lean run by the author). No theorem, no `sorry`, no `axiom`.

/-! # Loop-root probe on ACTUAL entries (EVIDENCE ONLY, logs only)

SRC_ARGW_SUPPLY_FREEZE.md rev3.1/rev3.2: option (b)'s `EntryKindOk` demands, at every `.state b n` env entry created
at a TYPED non-domain source binder, `n = 1 ∧ st.kinds[b]? = some k` (G12 conv/chain let, G20 loop `lam` binder,
the shared probe, and the wrapper's root lets). Whether an ACTUAL run creates `.state b n` with `n ≠ 1` at a typed
binder was not shown either way. This file RUNS the fuel reader (the doubling driver's final fuel, then the same
wrapper once more over a LOGGING copy of the fuel table) on corpus machine-route declarations with `Signal.loop`
(each has a kernel-checked endpoint: `#machine_endpoint` / `ShippingMachineCommand.generate`) and logs, per created
loop-root entry, one line

    LOOPROOT ENTRY <decl>: site=<lam|conv-let|chain-let|root-let> binder=<kind of the source binder> entry=<.state b n>
      class=<STATE1 TYPED kinds[b]=k | STATE1 TYPED kinds[b]!=k (MISMATCH) | STATE1 UNTYPED | STATEN … TYPED (FINDING …)
             | STATEN … UNTYPED>

* `site=lam`: the `loopBody` entry `.state b n` at the loop function's binder (`lamB`), i.e. the result of a
  `loopRoot` call (fresh `.state base n` or shared probe `.state b0 n`, FD:556/:590);
* `site=conv-let` / `chain-let`: the let binder receiving `mv` (FD:368-369, :517-518), recomputed with `readF` at the
  same fuel (the same answer as the logging table);
* `site=root-let`: a wrapper root let `(nm, ty, v)` with `v` a `Signal.loop` (FS:214-215), binder = `ty`.
A `FINDING` line (typed binder, `n ≠ 1`) would be an actual entry that option (b) EXCLUDES; it must be reported and
NOT excluded from FG. A `MISMATCH` line would refute the singleton supply `kinds[b] = k` on that run.

NOT CLAIMED: no theorem; coverage of other declarations; that the logging table equals `readF` (it is `fuel (step
senv)` with a side-effecting tap, `unsafe`, logs only); the production `partial` reader (O1). -/
namespace Tests.Gen3.LoopRootProbe
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel

def kindStr : Option MixedGateBinder → String
  | none => "none"
  | some .domain => "domain"
  | some .bool => "bool"
  | some (.bits w) => s!"bits {w}"

def valStr : MachVal → String
  | .state b n => s!".state {b} {n}"
  | .val _ => ".val"
  | .regs q => s!".regs {q}"
  | .handle i => s!".handle {i}"
  | .unit => ".unit"

def isTyped : Option MixedGateBinder → Bool
  | some .domain => false
  | some _ => true
  | none => false

/-- The class of a created entry against its source binder kind (`EntryKindOk`, ArgSupply3). -/
def classify (k : Option MixedGateBinder) (m : MachVal) (st : MachRead) : String :=
  match m with
  | .state b n =>
    if n == 1 then
      if isTyped k then
        (if st.kinds[b]? == k then "STATE1 TYPED kinds[b]=k" else "STATE1 TYPED kinds[b]!=k (MISMATCH)")
      else "STATE1 UNTYPED (no obligation)"
    else
      if isTyped k then s!"STATEN n={n} TYPED (FINDING: n != 1 at a typed binder)"
      else s!"STATEN n={n} UNTYPED (no obligation)"
  | .val _ => "VAL"
  | _ => "OTHER"

/-- The loop function's binder kind (`loopView?`'s `lam`, FD:280-283). -/
def lamKind (e : Lean.Expr) : Option MixedGateBinder :=
  match inlSpine e [] with
  | (_, [_, _, _, .lam _ t _ _]) => mixedGateBinderKind? t
  | _ => none

/-- Push one log line as a side effect and return `a` (logs only). -/
@[noinline] unsafe def tap {α : Type} (ref : IO.Ref (Array String)) (s : String) (a : α) : α :=
  unsafeBaseIO (do ref.modify (·.push s); pure a)

/-- A conv/chain `let` whose value floats to a `Signal.loop`: log the created entry at the let binder. -/
unsafe def noteLet {α : Type} (senv : StructEnv) (ref : IO.Ref (Array String)) (n : Nat) (site : String)
    (env : List MachVal) (ty v : Lean.Expr) (st : MachRead) (r : α) : α :=
  let v' := Sparkle.Compiler.MachRawSurface.rootFloat v
  match v' with
  | .letE .. => r
  | _ =>
    if v'.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      let k := mixedGateBinderKind? ty
      match (readF senv n (.loopRoot env v' st) : Option (Option (MachVal × MachRead))) with
      | some (some (mv, st')) =>
        tap ref s!"site={site} binder={kindStr k} entry={valStr mv} class={classify k mv st'}" r
      | some none => tap ref s!"site={site} binder={kindStr k} loopRoot=FAIL" r
      | none => tap ref s!"site={site} binder={kindStr k} loopRoot=OUT" r
    else r

/-- The tap of one answered block call. -/
unsafe def note (senv : StructEnv) (ref : IO.Ref (Array String)) (n : Nat) :
    (c : Call) → Option (RB c) → Option (RB c)
  | .loopRoot _ e _, r =>
    match (r : Option (Option (MachVal × MachRead))) with
    | some (some (mv, st')) =>
      tap ref s!"site=lam binder={kindStr (lamKind e)} entry={valStr mv} class={classify (lamKind e) mv st'}" r
    | some none => tap ref "site=lam loopRoot=FAIL" r
    | none => r
  | .conv env 0 (.letE _ ty v _ _) st, r => noteLet senv ref n "conv-let" env ty v st r
  | .chain env (.letE _ ty v _ _) st, r => noteLet senv ref n "chain-let" env ty v st r
  | _, r => r

/-- `fuel (step senv)` with the tap (same recursion as `readF`, FD:159-162 / :684). -/
unsafe def tracedF (senv : StructEnv) (ref : IO.Ref (Array String)) : Nat → (c : Call) → Option (RB c)
  | 0, _ => none
  | n + 1, c => note senv ref n c ((step senv c).run (tracedF senv ref n))

/-- The wrapper's root-let loops (FS:214-215). -/
unsafe def noteRoot (ref : IO.Ref (Array String)) (rk : List (Lean.Expr × Option MixedGateBinder)) :
    (c : Call) → Option (RB c) → Option (RB c)
  | .loopRoot _ e _, r =>
    match (r : Option (Option (MachVal × MachRead))) with
    | some (some (mv, st')) =>
      match rk.find? (·.1 == e) with
      | some (_, k) => tap ref s!"site=root-let binder={kindStr k} entry={valStr mv} class={classify k mv st'}" r
      | none => tap ref s!"site=root-loop(no root let found) entry={valStr mv}" r
    | _ => r
  | _, r => r

/-- The wrapper table (`wtab`, FS:74-76) over the logging block table. -/
unsafe def wtabT (senv : StructEnv) (ref : IO.Ref (Array String)) (n : Nat)
    (rk : List (Lean.Expr × Option MixedGateBinder)) : (c : WCall) → Option (WCall.Res c)
  | .norm e => machNormF n senv e
  | .blk c => noteRoot ref rk c (tracedF senv ref n c)

unsafe def runTracedImpl (senv : StructEnv) (entry : ConstantInfo) (n : Nat) : IO (Array String × String) := do
  let ref ← IO.mkRef (#[] : Array String)
  let rk : List (Lean.Expr × Option MixedGateBinder) :=
    match shapePre false [] entry senv with
    | some p =>
      match machNormF n senv p.e with
      | some en => (shapeMid senv p en).rootLets.map fun (_, ty, v) => (v, mixedGateBinderKind? ty)
      | none => []
    | none => []
  -- `IO.mkRef`'s argument is evaluated here, before the log is read (forces the run)
  let clsRef ← IO.mkRef (resClass ((shapeW false [] entry senv true).run (wtabT senv ref n rk)))
  let cls ← clsRef.get
  let logs ← ref.get
  pure (logs, cls)

@[implemented_by runTracedImpl]
opaque runTraced (senv : StructEnv) (entry : ConstantInfo) (n : Nat) : IO (Array String × String)

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- One declaration: the driver's answer and fuel, then the logged entries (deduplicated) and counts. -/
def probeDecl (label : String) (nm : Name) : TermElabM (Nat × Nat × Nat × Nat) := do
  let env ← getEnv
  let senv := structEnv env
  let ci ← getConstInfo nm
  let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
  let dr := driveShape defaultRounds 1 false [] entry senv
  logInfo m!"LOOPROOT PROBE {label}: driver={resClass dr.res} fuel={dr.finalFuel} doublings={dr.doublings}"
  let (logs, cls) ← runTraced senv entry dr.finalFuel
  let mut seen : Array String := #[]
  for l in logs do
    unless seen.contains l do seen := seen.push l
  for l in seen do
    logInfo m!"LOOPROOT ENTRY {label}: {l}"
  let nTyped1 := (seen.filter (hasSub · "STATE1 TYPED kinds[b]=k")).size
  let nMis := (seen.filter (hasSub · "MISMATCH")).size
  let nFind := (seen.filter (hasSub · "FINDING")).size
  let nUntyped := (seen.filter (hasSub · "UNTYPED")).size
  logInfo m!"LOOPROOT SUMMARY {label}: traced={cls} entries={seen.size} state1-typed-ok={nTyped1} mismatch={nMis} stateN-typed(FINDING)={nFind} untyped={nUntyped}"
  if nFind > 0 then
    logInfo m!"LOOPROOT FINDING {label}: an ACTUAL entry .state b n with n != 1 at a typed non-domain binder (option (b) excludes it; report, do NOT exclude from FG)"
  pure (seen.size, nTyped1, nMis, nFind)

/-- The probed declarations (corpus machine-route `Signal.loop` declarations with a kernel-checked endpoint). -/
def probeList : List (String × Name) :=
  [("wholeLoop", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.wholeLoop),
   ("wholeToggle", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.wholeToggle),
   ("counterLoop", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.counterLoop),
   ("accLoop", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.accLoop),
   ("loopPair", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.loopPair),
   ("divQ", ``Sparkle.Tests.Compiler.ShippingMachineLoopTest.divQ),
   ("bottleneckController", ``Sparkle.IP.YOLOv8.Blocks.Bottleneck.bottleneckController),
   ("dividerSignal", ``Sparkle.IP.RV32.Divider.dividerSignal),
   ("toggleL", ``Sparkle.Tests.Compiler.ShippingMachineSeqLoopTest.toggleL),
   ("outer", ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.outer),
   ("siblings", ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.siblings),
   ("withMemory", ``Sparkle.Tests.Compiler.ShippingMachineFuseTest.withMemory),
   ("quantModule", ``Sparkle.IP.Video.H264.QuantSynth.quantModule)]

run_cmd liftTermElabM do
  logInfo m!"LOOPROOT PROBE START: {probeList.length} declarations (EVIDENCE ONLY; logs only; not a theorem)"
  let mut tot := 0
  let mut ok1 := 0
  let mut mis := 0
  let mut fnd := 0
  for (label, nm) in probeList do
    let (a, b, c, d) ← probeDecl label nm
    tot := tot + a
    ok1 := ok1 + b
    mis := mis + c
    fnd := fnd + d
  logInfo m!"LOOPROOT PROBE TOTAL: entries={tot} state1-typed-ok={ok1} mismatch={mis} stateN-typed(FINDING)={fnd}"
  logInfo "LOOPROOT PROBE: evidence about these runs only; NOT coverage of the corpus, NOT L-RUN / L-FG, NOT a supply of LoopSrcKinds / LoopLetSrcKinds."

end Tests.Gen3.LoopRootProbe
