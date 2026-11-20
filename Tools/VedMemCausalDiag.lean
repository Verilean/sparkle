import Lean
import Tools.VedMemLoop

/-!
# `ved_causal` simp1 timing (DIAGNOSIS ONLY; not imported by any production module)

Imported only by a diagnosis case file.  With the env var `VED_DIAG` unset every `ved_loop_simp` runs exactly as in
production (the production macro is called directly).  With `VED_DIAG` set, at the `VED_DIAG_K`-th (default 1) `ved_loop_simp`
call that has the shape of the `ved_causal` simp1 (its lemma list holds `memory_val_succ`, no location) and whose goal has
a tree of more than `VED_DIAG_MIN` (default 1000000; 0 = every such goal) nodes, the simp1 is run ONCE through `Simp.main`
with wrapped `pre`/`post`/`dpre`/`dpost`, and the process is stopped:

  `VED DIAG STOP diagnostic_only reason=<fixed code>` on stderr, the measurement lines, then `IO.Process.exit 3`
  (never 0).  A stopped run is never a ledger row.

The simp1 syntax is the one the production macro expands `ved_loop_simp [...]` to (the production macro function is called
on the very syntax, so lemma list and config are the production ones by construction).

Measured: `totalMs` of the `Simp.main` call; `insideMs` = the time spent in `pre`/`post` (and `dpre`/`dpost`, reported
apart) calls at re-entry depth 0 (a nested call from a discharger / recursive simp is counted in `depthGt0Calls` only: its time
is inside the depth-0 call that contains it); recorded also when the call throws.  No size counting of results or
proofs, no message `toString`; only finite counters and head constant names.

Cooperative cancel (NOT a hard cap): every wrapper call compares the wall clock with `VED_DIAG_CAP_S` (default 300; `VED_DIAG_CAP_MS` overrides, for controls) and, after
it, throws a fixed error (sticky: later calls throw again, so a swallowing `try` inside simp does not cancel the cancel).  A
cancel can only happen at a pre/post call; the hard limits are the outer `timeout` and the RSS guard.
The state is restored in a `finally` path.  `VED_DIAG_AFTER=continue` (controls only) restores and carries on with the
production tactic instead of exiting.

Test hooks (controls): `VED_DIAG_THROW_AT=N` makes the N-th depth-0 pre/post call throw after its work;
`ved_diag_test [lemmas]` runs the measurement on the current goal with an arbitrary `simp [lemmas]` (always continues).
-/

namespace Tools.VedMemCausalDiag

open Lean Meta Elab Tactic

/-- finite counters of one measurement -/
structure Acc where
  t0 : IO.Ref Nat                      -- set when `Simp.main` starts
  capNs : Nat
  throwAt : Nat
  depth : IO.Ref Nat
  cancelled : IO.Ref Bool
  inNs : IO.Ref Nat
  inDNs : IO.Ref Nat
  calls : IO.Ref (Array Nat)           -- pre, post, dpre, dpost at depth 0
  deep : IO.Ref Nat                    -- calls at depth > 0
  n0 : IO.Ref Nat                      -- depth-0 pre/post calls so far (for the test throw)
  slow : IO.Ref (Array (Nat × Name × Nat))   -- (ns, head, kind) the slowest depth-0 calls
  heads : IO.Ref (Std.HashMap Name (Nat × Nat)) -- head -> (ns, calls), pre/post depth 0

def Acc.new (capMs throwAt : Nat) : IO Acc := do
  return { t0 := ← IO.mkRef 0, capNs := capMs * 1000000, throwAt, depth := ← IO.mkRef 0, cancelled := ← IO.mkRef false,
           inNs := ← IO.mkRef 0, inDNs := ← IO.mkRef 0, calls := ← IO.mkRef #[0, 0, 0, 0], deep := ← IO.mkRef 0,
           n0 := ← IO.mkRef 0, slow := ← IO.mkRef #[], heads := ← IO.mkRef {} }

def headName (e : Expr) : Name :=
  match e.getAppFn with
  | .const c _ => c
  | .proj .. => `_proj
  | .fvar .. => `_fvar
  | .lam .. => `_lam
  | .forallE .. => `_forall
  | .letE .. => `_let
  | .mdata .. => `_mdata
  | .lit .. => `_lit
  | _ => `_other

def kindName : Nat → String
  | 0 => "pre" | 1 => "post" | 2 => "dpre" | _ => "dpost"

/-- run `k` (a `pre`/`post`/`dpre`/`dpost`) timed at depth 0 only; the time is added also when `k` throws -/
def timed {α : Type} (a : Acc) (kind : Nat) (e : Expr) (k : Simp.SimpM α) : Simp.SimpM α := do
  let t ← IO.monoNanosNow
  if (← a.cancelled.get) || t - (← a.t0.get) > a.capNs then
    a.cancelled.set true
    throwError "ved_diag: cooperative cancel"
  if (← a.depth.get) > 0 then
    a.deep.modify (· + 1)
    return (← k)
  a.depth.set 1
  a.calls.modify fun c => c.modify kind (· + 1)
  try
    let r ← k
    if kind < 2 && a.throwAt > 0 then
      let n ← a.n0.modifyGet fun n => (n + 1, n + 1)
      if n == a.throwAt then throwError "ved_diag: test throw"
    return r
  finally
    let dt := (← IO.monoNanosNow) - t
    a.depth.set 0
    if kind < 2 then
      a.inNs.modify (· + dt)
      let h := headName e
      a.heads.modify fun m => let (n, c) := m.getD h (0, 0); m.insert h (n + dt, c + 1)
    else
      a.inDNs.modify (· + dt)
    let sl ← a.slow.get
    if sl.size < 10 || dt > (sl.back!).1 then
      a.slow.set ((sl.push (dt, headName e, kind)).qsort (fun x y => x.1 > y.1) |>.extract 0 10)

def wrap (a : Acc) (m : Simp.Methods) : Simp.Methods :=
  { m with
    pre := fun e => timed a 0 e (m.pre e)
    post := fun e => timed a 1 e (m.post e)
    dpre := fun e => timed a 2 e (m.dpre e)
    dpost := fun e => timed a 3 e (m.dpost e) }

/-- the real stderr (Lean isolates `IO.getStderr` while a command elaborates; a line written there is lost on `exit`) -/
def rawErr : IO IO.FS.Handle := IO.FS.Handle.mk "/dev/stderr" .append

def diagLine (l : String) : IO Unit := do
  let h ← rawErr
  h.putStrLn l
  h.flush

def fmtMs (ns : Nat) : String := s!"{ns / 1000000}"

def report (a : Acc) (totalNs : Nat) (reason : String) : IO Unit := do
  let inN ← a.inNs.get
  let inD ← a.inDNs.get
  let cs ← a.calls.get
  let deep ← a.deep.get
  let sl ← a.slow.get
  let hs := (← a.heads.get).toArray.qsort (fun x y => x.2.1 > y.2.1)
  let tot := totalNs / 1000000
  let ins := (inN + inD) / 1000000
  let cls :=
    if reason != "measured" then "unknown"
    else if ins * 3 > tot * 2 then "inside_dominated"
    else if ins * 3 < tot then "outside_dominated"
    else "mixed"
  let l1 := s!"VED DIAG totalMs={tot} insideMs={ins} (prepostMs={fmtMs inN} dprepostMs={fmtMs inD}) outsideMs={if tot ≥ ins then tot - ins else 0} totalUs={totalNs / 1000} insideUs={(inN + inD) / 1000} insideOverTotal={if tot == 0 then 0 else ins * 100 / tot}% class={cls}"
  let l2 := s!"VED DIAG calls depth0 pre={cs[0]!} post={cs[1]!} dpre={cs[2]!} dpost={cs[3]!} depthGt0Calls={deep} (not timed separately)"
  let l3 := "VED DIAG slowest depth0 calls: " ++ String.intercalate "; " (sl.toList.map fun (ns, h, k) => s!"{kindName k} {h} {fmtMs ns}ms")
  let l4 := "VED DIAG top heads by inside ms (pre/post depth0): " ++ String.intercalate "; " ((hs.toList.take 10).map fun (h, (ns, c)) => s!"{h} {fmtMs ns}ms/{c}")
  for l in [s!"VED DIAG STOP diagnostic_only reason={reason}", l1, l2, l3, l4] do
    diagLine l

/-- the measured `Simp.main` run of the syntax `simpStx` on the main goal; the state is restored afterwards (also on
exception).  Returns the reason code. -/
def measure (simpStx : Syntax) (capMs throwAt : Nat) : TacticM String := do
  let g ← getMainGoal
  let s ← saveState
  let a ← Acc.new capMs throwAt
  let totalRef ← IO.mkRef 0
  let reasonRef ← IO.mkRef "measured"
  try
    try
      g.withContext do
        let mc ← mkSimpContext simpStx (eraseLocal := false)
        let target ← instantiateMVars (← g.getType)
        let methods := wrap a (Simp.mkDefaultMethodsCore mc.simprocs)
        let t ← IO.monoNanosNow
        a.t0.set t
        try
          let _ ← Simp.main target mc.ctx (methods := methods)
        finally
          totalRef.set ((← IO.monoNanosNow) - t)
    catch e =>
      reasonRef.set (if (← a.cancelled.get) then "cooperative_cancel"
                     else if e.isRuntime then "runtime_exception" else "simp_exception")
    if (← a.cancelled.get) then reasonRef.set "cooperative_cancel"
  finally
    s.restore
  let reason ← reasonRef.get
  report a (← totalRef.get) reason
  return reason

/-- the production expansion of a `ved_loop_simp` syntax: the oldest macro registered for the kind -/
def prodExpansion (stx : Syntax) : TacticM Syntax := do
  let es := macroAttribute.getEntries (← getEnv) stx.getKind
  match es.getLast? with
  | some e => liftMacroM (e.value stx)
  | none => throwError "ved_diag: no production macro for {stx.getKind}"

initialize loopSeen : IO.Ref Nat ← IO.mkRef 0

def envNat (n : String) (d : Nat) : IO Nat := return ((← IO.getEnv n).bind String.toNat?).getD d

/-- the cooperative wall time in ms: `VED_DIAG_CAP_MS`, else `VED_DIAG_CAP_S` (default 300; `VED_DIAG_CAP_MS` overrides, for controls) seconds -/
def capMs : IO Nat := do
  match (← IO.getEnv "VED_DIAG_CAP_MS").bind String.toNat? with
  | some ms => return ms
  | none => return (← envNat "VED_DIAG_CAP_S" 300) * 1000

syntax (name := diagSimp) "ved_diag_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| ved_loop_simp [$ex,*] $[$loc]?) => `(tactic| ved_diag_simp [$ex,*] $[$loc]?)

@[tactic diagSimp] def evalDiagSimp : Tactic := fun stx => do
  -- the production syntax of this very call
  let orig := (stx.setKind ``Tools.VedU1Entry.vedLoopSimp).setArg 0 (mkAtom "ved_loop_simp ")
  let prod ← prodExpansion orig
  let isSimp1 := stx[4].isNone && (stx[2].getSepArgs.any fun s => (s.reprint.getD "").contains "memory_val_succ")
  if isSimp1 && (← IO.getEnv "VED_DIAG").isSome then
    let g ← getMainGoal
    let e0 ← g.withContext do instantiateMVars (← g.getType)
    if Tools.VedU1Loop.treeSizeVal e0 > (← envNat "VED_DIAG_MIN" 1000000) then
      let n ← loopSeen.modifyGet fun n => (n + 1, n + 1)
      if n == (← envNat "VED_DIAG_K" 1) then
        let reason ← measure prod (← capMs) (← envNat "VED_DIAG_THROW_AT" 0)
        if (← IO.getEnv "VED_DIAG_AFTER") == some "continue" then
          diagLine s!"VED DIAG continue diagnostic_only reason={reason}"
        else
          IO.Process.exit 3
  evalTactic prod

/-- control: the measurement on the current goal with `simp [lemmas]`; always continues (state restored) -/
elab "ved_diag_test " "[" ex:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let stx ← `(tactic| simp [$ex,*])
  let reason ← measure stx (← capMs) (← envNat "VED_DIAG_THROW_AT" 0)
  diagLine s!"VED DIAG test-continue diagnostic_only reason={reason}"

end Tools.VedMemCausalDiag
