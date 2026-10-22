import Tools.ShippingInitAlloc
import Tests.Compiler.ChildVertAuditTest
-- BUILT (unit RT4c: rt4c1 exit 0, rt4c2 see report; pure checker, MKREF-filtered counts, negative tests); previous BUILT (unit RT4b: strict evidence mode, seq/name check, finally-cleanup; rt4b1 exit 0, INIT TRACE OK); previous: BUILT (unit RT4): rt4c, rt4d, rt4e exit 1 (test-file syntax/type errors); rt4f, rt4g exit 0; rt4h exit 0 (final, shim source embedded; INIT TRACE OK). EVIDENCE + audit; proves none of the premises.

/-! Unit RT4 (L9f).
(1) Audits of `xfer_of_alloc` / `startContents_session_init_alloc` (axioms, closure, exact Prop-binder head list;
conclusion and hypothesis types compared by isDefEq with the L9e statement; mutations rejected).
(2) By TYPES: which declarations mention `ST.Prim.mkRef`/`ST.mkRef`/`IO.mkRef`; whether any field of `RefLawsAOps`
or any heap-model declaration does. This is a scan of the imported environment of this test, nothing more.
(3) EXECUTED-TRACE evidence (target-only, in a CHILD `lean` process): the OK / SKIPPED result is logged
separately; SKIPPED is NOT evidence. The child imports `Sparkle.Compiler.Elab` with the natively compiled
`libsparkle_Sparkle.so` loaded, under an `LD_PRELOAD` shim (`shimSource` below (written to a temp dir)) that logs
`lean_st_mk_ref`/`set`/`swap`/`reset` (cell address, call order). The child prints the addresses of the three
registered refs; the test checks their `mkRef` events, the order, that no other write hit them, and that no cell
address was allocated twice in the window. Limits: one process, one run (addresses vary per run); only calls through
the dynamic symbol table are seen (not `lean_st_ref_get`, not runtime-internal calls); the child is NOT the process
that elaborates this file; the `.so` is whatever is in `.lake/build/lib`; the `Other` steps between are only
counted, not proved to satisfy `OthersFrameRefs`; no model heap is related; runtime fit NOT PROVEN.
Scope (integrator wording, par/int-r47, per review): the shim's mutex only makes the LOG sequence numbers consecutive; it does not
establish the execution order of the primitives as a whole, nor dlsym/concurrency safety. The strict-mode FAILURE paths (seq gap, unknown
event, missing tracked MKREF, non-zero child exit) are exercised only by SYNTHETIC inputs to the pure checker `checkTraceResult` (not by fault injection into
the real child run). The per-interval MKREF counts filter on the event name MKREF. OK = single-run evidence; InitOrder holding and runtime fit are NOT proved. -/

open Lean Meta Elab in
run_meta do
  for n in [``Tools.ShippingInitAlloc.xfer_of_alloc, ``Tools.ShippingInitAlloc.startContents_session_init_alloc,
      ``Tools.ShippingInitAlloc.xfer_iff_rxfer, ``Tools.ShippingInitAlloc.rxfer_of_alloc] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
      [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
       `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
    logInfo m!"INIT-ALLOC AUDIT OK: {n}: standard axioms; closure {cl.size} constants"

open Lean Meta Elab in
def propHeadsRT4 (n : Name) : MetaM (List String) := do
  let some ci := (← getEnv).find? n | throwError "{n} unknown"
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        out := out ++ [(t.getAppFn.constName?.map (·.toString)).getD "?"]
    return out

open Lean Meta Elab in
run_meta do
  let n := ``Tools.ShippingInitAlloc.startContents_session_init_alloc
  let hs ← propHeadsRT4 n
  let exp := ["Tools.ShippingChildInvA.AdmCtx", "Tools.ShippingChildDepthC.BodyStepC",
    "Tools.ShippingStartWorldA2.OtherCodeKeeps",
    "Tools.ShippingInitFrame.InitOrder", "Tools.ShippingInitAlloc.MkDepthRelInv",
    "Tools.ShippingInitAlloc.MkCacheRelInv", "Tools.ShippingInitAlloc.MkSynthRelInv",
    "Tools.ShippingInitFrame.OthersFrameRefs",
    "Tools.ShippingStartAtLoad.InitHeapRel", "Tools.ShippingStartAtLoad.GetSpec",
    "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?",
    "Tools.ShippingStartWorldA2.Chain"]
  unless hs == exp do throwError "BINDER AUDIT FAILED: {hs}"
  if hs.contains "Tools.ShippingInitFrame.InitHeapRelXfer" then throwError "hxfer still assumed"
  let h2 ← propHeadsRT4 ``Tools.ShippingInitAlloc.xfer_of_alloc
  unless h2 == ["Tools.ShippingInitFrame.OthersFrameRefs", "Tools.ShippingInitAlloc.MkDepthRelInv",
      "Tools.ShippingInitAlloc.MkCacheRelInv", "Tools.ShippingInitAlloc.MkSynthRelInv"] do
    throwError "BINDER AUDIT FAILED (xfer_of_alloc): {h2}"
  logInfo m!"binder audit (exact Prop-binder head lists): session_init_alloc {hs}; xfer_of_alloc {h2}. The allocation premises REPLACE `InitHeapRelXfer` (one premise became three); NOT a discharge"

open Lean Meta Elab Term in
run_elab do
  let n := ``Tools.ShippingInitAlloc.startContents_session_init_alloc
  let ci ← getConstInfo n
  let ci0 ← getConstInfo ``Tools.ShippingInitSession.startContents_session_init
  forallTelescope ci.type fun xs concl => do
    let fv (nm : Name) : MetaM Expr := do
      for x in xs do
        if (← x.fvarId!.getUserName) == nm then return x
      throwError "binder {nm} not found"
    let mk (src : String) : TermElabM Expr := do
      let stx ← match Parser.runParserCategory (← getEnv) `term src with
        | .ok s => pure s | .error e => throwError e
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let good ← mk "(O.quiet w ∧ Tools.ShippingStartWorldA.StartContents w)"
    unless ← isDefEq concl good do throwError "AUDIT FAILED: conclusion {concl}"
    let hd ← inferType (← fv `hd)
    let hc ← inferType (← fv `hc)
    let hms ← inferType (← fv `hms)
    unless ← isDefEq hd (← mk "(Tools.ShippingInitAlloc.MkDepthRelInv R)") do throwError "hd {hd}"
    unless ← isDefEq hc (← mk "(Tools.ShippingInitAlloc.MkCacheRelInv R)") do throwError "hc {hc}"
    unless ← isDefEq hms (← mk "(Tools.ShippingInitAlloc.MkSynthRelInv R)") do throwError "hms {hms}"
    if ← isDefEq hd hc then throwError "depth/cache allocation premises identified"
    if ← isDefEq hc hms then throwError "cache/synth allocation premises identified"
    if ← isDefEq hd hms then throwError "depth/synth allocation premises identified"
    let hf ← inferType (← fv `hf)
    unless ← isDefEq hf (← mk "(Tools.ShippingInitFrame.OthersFrameRefs R Other₀)") do throwError "hf {hf}"
    -- same conclusion as the L9e statement, whose binder `hs` (chain from w0) is kept
    forallTelescope ci0.type fun ys concl0 => do
      unless ← isDefEq (← inferType (← fv `hs)).getAppFn (← inferType ys.back!).getAppFn do
        throwError "chain head differs from L9e"
      let _ := concl0
    logInfo m!"INIT-ALLOC CONCLUSION AUDIT OK (conclusion; types of hd, hc, hms, hf by isDefEq; the three allocation premises pairwise distinct); NOT a whole forall-type identity"

/-! ## (2) which declarations mention `mkRef` -/
open Lean in
def mkRefdMentioned (env : Environment) : Bool :=
  match env.find? ``Tools.ShippingChildFresh.MkRefd with
  | some ci => (ci.value?.map (·.getUsedConstants)).getD #[] |>.any ([``ST.Prim.mkRef, ``ST.mkRef, ``IO.mkRef].contains ·)
  | none => false

open Lean Meta Elab in
run_meta do
  let env ← getEnv
  let mk : List Name := [``ST.Prim.mkRef, ``ST.mkRef, ``IO.mkRef]
  let mut hitsT : Array Name := #[]
  let mut hitsS : Nat := 0
  let mut model : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let root := n.getRoot
    unless root == `Tools || root == `Sparkle do continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    if used.any (mk.contains ·) then
      if root == `Tools then hitsT := hitsT.push n else hitsS := hitsS + 1
      if (`Tools.ShippingHeapModel).isPrefixOf n then model := model.push n
  let hitsTs := hitsT.qsort Name.lt
  logInfo m!"declarations in `Tools.*` mentioning mkRef ({hitsTs.size}); `Sparkle.*` declarations mentioning it (compiler side): {hitsS}"
  unless model.isEmpty do throwError "heap-model declaration mentions mkRef: {model}"
  -- which of them relate an mkRef result to the three registered constants?
  let reg : List Name := [``Sparkle.Compiler.Elab.sparkleSynthDepth, ``Sparkle.Compiler.Elab.sparkleChildCache,
    ``Sparkle.Compiler.Elab.sparkleChildSynth]
  let mut relate : Array Name := #[]
  for n in hitsTs do
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    if used.any (reg.contains ·) && !(`Tools.ShippingChildInv.Framed).isPrefixOf n && !(`Tools.ShippingChildInvA.FramedA).isPrefixOf n then relate := relate.push n
  unless relate.toList == [``Tools.ShippingStartAtLoad.MkRefTrace] do
    throwError "mkRef-and-registered-constant mentioned together by: {relate}"
  -- fields of RefLawsAOps
  let some ci := env.find? ``Tools.ShippingChildInvA.RefLawsAOps | throwError "RefLawsAOps unknown"
  let used := ci.type.getUsedConstants
  let some (.inductInfo iv) := env.find? ``Tools.ShippingChildInvA.RefLawsAOps | throwError "not inductive"
  let mut fieldHits : Array Name := #[]
  for c in iv.ctors do
    let some cci := env.find? c | continue
    if cci.type.getUsedConstants.any (mk.contains ·) then fieldHits := fieldHits.push c
  unless fieldHits.isEmpty && !used.any (mk.contains ·) do throwError "RefLawsAOps mentions mkRef"
  match env.find? ``ST.Prim.mkRef with
  | some (.opaqueInfo _) => pure ()
  | _ => throwError "ST.Prim.mkRef is not an opaque constant"
  unless Lean.isExtern env ``ST.Prim.mkRef do throwError "ST.Prim.mkRef is not extern"
  let some fr := env.find? ``Tools.ShippingChildInvA.FramedA.localMk | throwError "FramedA.localMk unknown"
  unless fr.type.getUsedConstants.any (mk.contains ·) do throwError "FramedA.localMk does not mention mkRef"
  unless mkRefdMentioned env do throwError "MkRefd does not mention mkRef"
  logInfo m!"BY TYPES: `ST.Prim.mkRef` is an `@[extern] opaque` (no specification). No constructor of `RefLawsAOps` and no `Tools.ShippingHeapModel.*` declaration mentions mkRef directly. The only `Tools.*` declaration (apart from the generated recursors of the `Framed`/`FramedA` frame inductives, which mention the cache refs in their constructors) that mentions BOTH mkRef and a registered constant is the unused `MkRefTrace` (OPEN). O's frame law mentions mkRef only via the `FramedA` frame inductive (`localMk` constructor checked here; no `RefLawsAOps` constructor type mentions it directly): a MetaM-run frame statement (under AdmCtx/quiet, about cv/sv/dv), not the module-initialisation mkRef and not freshness. `MkRefd` is a HISTORY (some mkRef run returned this ref), explicitly not distinctness from the tracked refs. The heap model's `alloc` allocates `other n` cells only; the three tracked cells are heap fields."

/-! ## (3) executed trace in a child process -/
open Lean Meta Elab in
def hexNat? (s : String) : Option Nat :=
  let s := if s.startsWith "0x" then (s.drop 2).toString else s
  s.foldl (fun acc c => acc.bind fun a =>
    if c.isDigit then some (a * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (a * 16 + (c.toNat - 'a'.toNat + 10)) else none) (some 0)

/-- `.error reason` = SKIPPED; `.ok report` = OK (checks passed); an `IO` error = FAILED. -/
def shimSource : String := "/* Unit RT4 (test-only): LD_PRELOAD shim that logs the exported Lean ST.Ref primitives (mk/set/swap/reset)
   with the cell address, in call order, to the file named by $SPARKLE_REF_TRACE. It forwards every call
   unchanged. Used only by Tests/Compiler/InitTraceTest.lean on a CHILD `lean` process. It sees only calls that
   go through the dynamic symbol table (e.g. from a loaded precompiled module .so); calls resolved inside the
   Lean runtime itself, `lean_st_ref_get`, and inlined code are NOT logged. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
typedef void* o;
#define EXP __attribute__((visibility(\"default\")))
static FILE* lf; static unsigned long seq; static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
#define LOG(k, r) do { pthread_mutex_lock(&mu); L(); fprintf(lf, \"%lu \" k \" %p\\n\", seq++, (void*)(r)); pthread_mutex_unlock(&mu); } while (0)
static void L(void) {
  if (!lf) { const char* p = getenv(\"SPARKLE_REF_TRACE\"); lf = p ? fopen(p, \"a\") : NULL; if (!lf) lf = stderr; setvbuf(lf, NULL, _IOLBF, 0); }
}
EXP o lean_st_mk_ref(o a) { static o (*f)(o); if (!f) f = dlsym(RTLD_NEXT, \"lean_st_mk_ref\"); o r = f(a); LOG(\"MKREF\", r); return r; }
EXP o lean_st_ref_set(o r, o a) { static o (*f)(o, o); if (!f) f = dlsym(RTLD_NEXT, \"lean_st_ref_set\"); LOG(\"SET\", r); return f(r, a); }
EXP o lean_st_ref_swap(o r, o a) { static o (*f)(o, o); if (!f) f = dlsym(RTLD_NEXT, \"lean_st_ref_swap\"); LOG(\"SWAP\", r); return f(r, a); }
EXP o lean_st_ref_reset(o r) { static o (*f)(o); if (!f) f = dlsym(RTLD_NEXT, \"lean_st_ref_reset\"); LOG(\"RESET\", r); return f(r); }
"

/-- PURE trace checker over the child's exit code, its combined stdout/stderr and the trace-file contents
(`none` = file absent). Every failure is an `.error` (strict evidence mode). -/
def checkTraceResult (exitCode : UInt32) (out : String) (logText : Option String) : Except String String := do
  if exitCode != 0 then throw s!"child lean exited {exitCode}: {out.take 400}"
  let some addrLine := (out.splitOn "\n").find? (·.startsWith "ADDR ") | throw s!"no ADDR line: {out.take 400}"
  let ws := addrLine.splitOn " "
  let bad := s!"malformed ADDR line {addrLine}"
  unless ws.length == 7 && ws[1]? == some "depth" && ws[3]? == some "cache" && ws[5]? == some "synth" do throw bad
  let some ad := (ws[2]?).bind String.toNat? | throw bad
  let some ac := (ws[4]?).bind String.toNat? | throw bad
  let some as_ := (ws[6]?).bind String.toNat? | throw bad
  unless out.contains "SYNTH_SOME true DEPTH 0 CACHE_EMPTY true" do
    throw s!"end-state probe line unexpected: {out.take 400}"
  let some logText := logText | throw "no trace file written (interposition ineffective)"
  let lines := (logText.splitOn "\n").filter (· ≠ "")
  let allowed := ["MKREF", "SET", "SWAP", "RESET"]
  let mut ev : Array (String × Nat) := #[]
  for l in lines do
    match l.splitOn " " with
    | [sq, k, a] =>
      -- sequence numbers must be exactly 0,1,2,... and the event name in the allowed set
      unless sq.toNat? == some ev.size do
        throw s!"TRACE FAIL: sequence number not consecutive (expected {ev.size}): {l}"
      unless allowed.contains k do throw s!"TRACE FAIL: unknown event name in {l}"
      let some v := hexNat? a | throw s!"bad trace line {l}"
      ev := ev.push (k, v)
    | _ => throw s!"bad trace line {l}"
  let idxOf (a : Nat) : Array Nat := Id.run do
    let mut o := #[]
    for h : i in [0:ev.size] do
      if ev[i].1 == "MKREF" && ev[i].2 == a then o := o.push i
    return o
  let mkIdx := [ad, ac, as_].map fun a => (idxOf a).toList
  let [[id], [ic], [is]] := mkIdx | throw s!"TRACE FAIL: MKREF events of depth/cache/synth refs: {mkIdx}"
  unless id < ic && ic < is do throw s!"TRACE FAIL: order {id} {ic} {is}"
  let mkAddrs := (ev.filter (·.1 == "MKREF")).map (·.2)
  unless (mkAddrs.toList.eraseDups.length == mkAddrs.size) do
    throw "TRACE FAIL: a cell address was allocated twice in the window"
  let tracked := [ad, ac, as_]
  let mut wr : Array (Nat × String × Nat) := #[]
  for h : i in [0:ev.size] do
    if ev[i].1 != "MKREF" && tracked.contains ev[i].2 then wr := wr.push (i, ev[i].1, ev[i].2)
  match wr.toList with
  | [(iw, "SET", a)] =>
    unless a == as_ && iw > is do throw s!"TRACE FAIL: the one write is not the synth set after its mkRef: {wr}"
    let cnt (lo hi : Nat) : Nat := (((ev.toList.take hi).drop lo).filter (·.1 == "MKREF")).length
    let beforeD := cnt 0 id
    let betweenDC := cnt (id + 1) ic
    let betweenCS := cnt (ic + 1) is
    let afterSynth := cnt (is + 1) iw
    let otherWrites := (ev.toList.filter fun e => e.1 != "MKREF" && !tracked.contains e.2).length
    return s!"events {ev.size} (sequence numbers consecutive, names in {allowed}); MKREF index depth={id} < cache={ic} < synth={is}; the only write to the three cells is SET on the synth cell at event {iw} (after the synth MKREF); other-cell MKREFs (counted by FILTERING on the event name MKREF, not by index difference) before depth / between depth and cache / between cache and synth / between synth and the set: {beforeD} / {betweenDC} / {betweenCS} / {afterSynth}; writes to other cells in the window: {otherWrites}; all {mkAddrs.size} MKREF addresses distinct"
  | _ => throw s!"TRACE FAIL: writes to the three cells: {wr}"


/-- Everything after the prerequisites are known present: EVERY failure here throws (strict evidence mode). -/
def runInitTraceBody (cwd : System.FilePath) (lean leanc : System.FilePath) (tmp : System.FilePath) : IO String := do
  let lib : System.FilePath := cwd / ".lake/build/lib/libsparkle_Sparkle.so"
  let libdir : System.FilePath := cwd / ".lake/build/lib/lean"
  let src := tmp / "refshim.c"
  IO.FS.writeFile src shimSource
  let shim := tmp / "refshim.so"
  let log := tmp / "refs.log"
  let c ← IO.Process.output { cmd := leanc.toString, args := #["-shared", "-fPIC", "-O1", "-fvisibility=default",
    src.toString, "-o", shim.toString] }
  unless c.exitCode == 0 && (← shim.pathExists) do
    throw (IO.userError s!"shim compile failed (exit {c.exitCode}): {c.stderr}")
  let probe := tmp / "probe.lean"
  IO.FS.writeFile probe "import Sparkle.Compiler.Elab
open Sparkle.Compiler.Elab
#eval show IO Unit from do
  IO.eprintln s!\"ADDR depth {ptrAddrUnsafe sparkleSynthDepth} cache {ptrAddrUnsafe sparkleChildCache} synth {ptrAddrUnsafe sparkleChildSynth}\"
  IO.eprintln s!\"SYNTH_SOME {(← sparkleChildSynth.get).isSome} DEPTH {← sparkleSynthDepth.get} CACHE_EMPTY {(← sparkleChildCache.get).isEmpty}\"
"
  let spec : IO.Process.SpawnArgs :=
    { cmd := lean.toString
      args := #[s!"--load-dynlib={lib}", probe.toString]
      cwd := some tmp
      env := #[("LD_PRELOAD", some shim.toString), ("SPARKLE_REF_TRACE", some log.toString),
        ("LEAN_PATH", some libdir.toString)] }
  let r ← IO.Process.output spec
  let out := r.stdout ++ "\n" ++ r.stderr
  let logText ← if ← log.pathExists then pure (some (← IO.FS.readFile log)) else pure none
  match checkTraceResult r.exitCode out logText with
  | .ok rep => return rep
  | .error e => throw (IO.userError e)

/-- Runs `body` on a fresh temp dir and removes the dir on EVERY path (normal return or exception). -/
def withTmpDir {α} (body : System.FilePath → IO α) : IO α := do
  let tmp ← IO.FS.createTempDir
  try body tmp
  finally IO.FS.removeDirAll tmp

/-- `.error reason` = SKIPPED, only when a prerequisite (libsparkle `.so`, `leanc`) is genuinely absent;
`.ok report` = OK; any other failure is an `IO` error (FAILED). Temp dir removed on every path. -/
def runInitTrace : IO (Except String String) := do
  let cwd ← IO.currentDir
  let lib : System.FilePath := cwd / ".lake/build/lib/libsparkle_Sparkle.so"
  let lean ← IO.appPath
  let some bindir := lean.parent | return .error "no parent of lean executable"
  let leanc := bindir / "leanc"
  for p in [lib, leanc] do
    unless ← p.pathExists do return .error s!"prerequisite {p} not present"
  return .ok (← withTmpDir (runInitTraceBody cwd lean leanc))

open Lean Meta Elab in
run_meta do
  match ← (runInitTrace).toBaseIO with
  | .ok (.ok rep) => logInfo m!"INIT TRACE OK (executed, child process, LD_PRELOAD shim): {rep}"
  | .ok (.error why) => logInfo m!"INIT TRACE SKIPPED (NOT evidence): {why}"
  | .error e => throwError "INIT TRACE FAILED: {e}"

/-! ## Limited negative tests of the strict mode (synthetic inputs; the real run above is untouched) -/
def goodLog : String := "0 MKREF 0x10\n1 MKREF 0x20\n2 MKREF 0x30\n3 MKREF 0x40\n4 SET 0x30\n"
def goodOut : String := "ADDR depth 16 cache 32 synth 48\nSYNTH_SOME true DEPTH 0 CACHE_EMPTY true\n"

open Lean Meta Elab in
run_meta do
  -- sanity: the synthetic good input is accepted, so the rejections below are due to the injected fault
  match checkTraceResult 0 goodOut (some goodLog) with
  | .ok r => logInfo m!"negative-test baseline (synthetic good trace) accepted: {r}"
  | .error e => throwError "negative-test baseline rejected: {e}"
  let cases : List (String × Except String String) := [
    ("seq gap", checkTraceResult 0 goodOut (some "0 MKREF 0x10\n2 MKREF 0x20\n3 MKREF 0x30\n4 SET 0x30\n")),
    ("unknown event name", checkTraceResult 0 goodOut (some "0 MKREF 0x10\n1 MKREF 0x20\n2 FROB 0x99\n3 MKREF 0x30\n4 SET 0x30\n")),
    ("missing tracked MKREF", checkTraceResult 0 goodOut (some "0 MKREF 0x10\n1 MKREF 0x20\n2 SET 0x30\n")),
    ("non-zero child exit", checkTraceResult 1 goodOut (some goodLog))]
  for (nm, r) in cases do
    match r with
    | .error e => logInfo m!"negative test {nm}: checker returned FAILED as expected: {e.take 120}"
    | .ok _ => throwError "NEGATIVE TEST FAILED: {nm} was accepted"
  -- temp dir removed on the exception path and on the normal path
  let seen ← IO.mkRef (none : Option System.FilePath)
  let r ← (withTmpDir fun d => do seen.set (some d); (throw (IO.userError "injected") : IO Unit)).toBaseIO
  let some d ← seen.get | throwError "temp dir not created"
  unless r.toOption.isNone do throwError "injected failure not propagated"
  if ← d.pathExists then throwError "temp dir NOT removed on the failure path"
  let d2 ← withTmpDir fun d => do IO.FS.writeFile (d / "f") "x"; pure d
  if ← d2.pathExists then throwError "temp dir NOT removed on the normal path"
  logInfo m!"negative tests OK: seq gap, unknown event, missing tracked MKREF, non-zero child exit each give FAILED; temp dir removed on failure and normal paths. LIMITED: synthetic inputs to the pure checker, not fault injection into the real child run"
