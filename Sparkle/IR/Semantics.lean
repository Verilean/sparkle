/-
  Sparkle IR — mathematical semantics (proof-facing).

  A TOTAL evaluator for the scalar fragment of `Expr`, intended as the
  denotation that certified-roundtrip theorems are stated against:

      ⟦ lower (emit x) ⟧ = ⟦ x ⟧

  Design notes, in order of importance:

  * TOTAL, not `partial`.  A `partial def` produces no unfolding
    equations, so nothing can be proven about it — this is why the
    shipping pipeline (73 `partial def`s across Parser/Lower/Verilog/
    Optimize) cannot be the direct subject of theorems.  The verified
    core is written total; the shipping code is tied to it by
    cross-checking tests (verified-core / validated-shell split).

  * Values are `Nat` with EXPLICIT masking to the context width, not
    `BitVec n`.  The IR is width-annotated at consts/slices only, so a
    width-indexed value type would force every theorem through `Σ n,
    BitVec n` casts.  `Nat`+mask mirrors what both backends actually
    compute (CSim's `& mask` discipline, Verilog's context truncation)
    and keeps lemmas cast-free.  Two-state only: X/Z are outside the
    model, exactly as in CSim.

  * `Env` maps names to values, `WEnv` to widths.  Refs are looked up
    unmasked — well-formedness (every stored value already masked) is a
    hypothesis of the preservation theorems, not re-enforced per read.

  * The fragment: const/ref, the bitwise/arith/compare/shift/mux ops,
    concat, and constant-bound slice.  `sliceDim` (symbolic widths) and
    `index` (memories) return `none`; they enter the semantics when the
    proof reaches memories.
-/

import Sparkle.IR.AST

namespace Sparkle.IR.Semantics

open Sparkle.IR.AST

abbrev Env := String → Nat
abbrev WEnv := String → Nat

/-- Truncate to `w` bits. -/
def mask (w : Nat) (v : Nat) : Nat := v % (2 ^ w)

/-- Two's-complement interpretation of a masked value, for signed ops. -/
def toSigned (w : Nat) (v : Nat) : Int :=
  if v < 2 ^ (w - 1) then (v : Int) else (v : Int) - (2 ^ w : Nat)

/-- Width of an expression under a width environment (the proof-facing
    twin of the backends' `inferExprWidth`; binary ops take the MAX of
    their operands, matching hardware and the fixed CSim rule). -/
def widthOf (we : WEnv) : Expr → Nat
  | .const _ w => w
  | .ref n => we n
  | .op .mux args =>
    match args with
    | [_, t, _] => widthOf we t
    | _ => 0
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _ | .op .le_s _
  | .op .gt_u _ | .op .gt_s _ | .op .ge_u _ | .op .ge_s _ => 1
  | .op .not args =>
    match args with
    | [a] => widthOf we a
    | _ => 0
  | .op _ args =>
    match args with
    | [a, b] => max (widthOf we a) (widthOf we b)
    | [a] => widthOf we a
    | _ => 0
  | .concat args => go args
  | .slice _ hi lo => hi - lo + 1
  | .sliceDim _ _ _ => 0
  | .index _ _ => 0
where
  go : List Expr → Nat
    | [] => 0
    | a :: rest => widthOf we a + go rest

/-- Evaluate one operator over already-evaluated, already-masked operand
    values.  `w` is the result's context width. -/
def evalOp (we : WEnv) (operator : Operator) (args : List Expr)
    (vals : List Nat) (w : Nat) : Option Nat :=
  match operator, args, vals with
  | .and, _, [a, b] => some (mask w (a &&& b))
  | .or,  _, [a, b] => some (mask w (a ||| b))
  | .xor, _, [a, b] => some (mask w (a ^^^ b))
  | .not, [x], [a] =>
    let wx := widthOf we x
    some (mask wx (a ^^^ (2 ^ wx - 1)))
  | .add, _, [a, b] => some (mask w (a + b))
  | .sub, _, [a, b] => some (mask w (a + (2 ^ w - mask w b)))
  | .mul, _, [a, b] => some (mask w (a * b))
  | .eq,  _, [a, b] => some (if a = b then 1 else 0)
  | .lt_u, _, [a, b] => some (if a < b then 1 else 0)
  | .le_u, _, [a, b] => some (if a ≤ b then 1 else 0)
  | .gt_u, _, [a, b] => some (if b < a then 1 else 0)
  | .ge_u, _, [a, b] => some (if b ≤ a then 1 else 0)
  | .lt_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc a < toSigned wc b then 1 else 0)
  | .le_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc a ≤ toSigned wc b then 1 else 0)
  | .gt_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc b < toSigned wc a then 1 else 0)
  | .ge_s, [x, y], [a, b] =>
    let wc := max (widthOf we x) (widthOf we y)
    some (if toSigned wc b ≤ toSigned wc a then 1 else 0)
  | .shl, _, [a, b] => some (mask w (a <<< b))
  | .shr, _, [a, b] => some (a >>> b)
  | .asr, [x, _], [a, b] =>
    let wx := widthOf we x
    let s := toSigned wx a
    some (mask wx (Int.toNat ((s >>> b) % (2 ^ wx : Nat))))
  | .mux, _, [c, t, f] => some (if c ≠ 0 then t else f)
  | .neg, _, [a] => some (mask w (2 ^ w - mask w a))
  | _, _, _ => none

mutual
/-- Total evaluator for the scalar fragment.  `none` = outside the
    fragment (symbolic widths, memory reads) or malformed arity. -/
def evalExpr (we : WEnv) (env : Env) : Expr → Option Nat
  | .const v w =>
    -- Two's-complement encode negatives into w bits, like the emitters.
    some (mask w (Int.toNat (((v % (2 ^ w : Nat)) + (2 ^ w : Nat)) % (2 ^ w : Nat))))
  | .ref n => some (env n)
  | .op operator args => do
    let vals ← evalList we env args
    evalOp we operator args vals (widthOf we (.op operator args))
  | .concat args => do
    let vals ← evalList we env args
    -- MSB-first: the FIRST element lands in the high bits.
    some (go args vals)
  | .slice e hi lo => do
    let v ← evalExpr we env e
    some (mask (hi - lo + 1) (v >>> lo))
  | .sliceDim _ _ _ => none
  | .index _ _ => none
where
  go : List Expr → List Nat → Nat
    | a :: as, v :: vs =>
      let restW := (as.zip vs).foldl (fun acc (p : Expr × Nat) => acc + widthOf we p.1) 0
      (mask (widthOf we a) v) <<< restW ||| go as vs
    | _, _ => 0

def evalList (we : WEnv) (env : Env) : List Expr → Option (List Nat)
  | [] => some []
  | a :: rest => do
    let v ← evalExpr we env a
    let vs ← evalList we env rest
    some (v :: vs)
end

/- ------------------------------------------------------------------ -/
/- Module-level step semantics (M1).

   One clock cycle of a module, in two phases exactly mirroring the
   backends' eval/tick split:

   * `evalAssigns` — combinational elaboration: fold the body's assigns
     IN ORDER over an environment seeded with inputs and current
     register values.  Correctness relies on the body being
     topologically sorted, which is a WELL-FORMEDNESS assumption here
     and a guarantee of `topoSortBody` on the shipping pipeline.

   * `regNexts` — the register phase: each register's next value is
     `if reset ≠ 0 then init else ⟦input⟧` under the POST-elaboration
     environment.  Reset KIND (sync/async) is deliberately ignored: in
     the cycle-level model both kinds sample reset once per cycle, which
     is also why the parser losing the `or posedge rst` sensitivity is
     semantically inert.

   Memories follow the `Stmt.memory` contract documented in the AST:
   all ports share the clock, reads see the state BEFORE this cycle's
   writes (read-old), and simultaneous writes to the same address are
   resolved by port order (last enabled port wins).  Memory state is an
   `MEnv`; combinational reads extend the environment during
   elaboration, synchronous reads latch like registers, and writes are
   evaluated under the POST-elaboration environment (the backends'
   tick phase).

   INSTANCES are no-ops in this OPEN-module semantics: an instance's
   outputs are free inputs of the enclosing module (driven by the
   seed), so the trace theorems quantify over EVERY behavior of the
   instantiated modules.  The actual composition is covered dynamically
   by the hierarchical co-sim; a closed hierarchical semantics is
   future work. -/

/-- Memory state: array contents by memory name. -/
abbrev MEnv := String → Nat → Nat

/-- Combinational read ports: extend the env with `rd ↦ mem[addr]`,
    in port order (mirrors the emitted `assign` per port). -/
def comboReads (we : WEnv) (mems : MEnv) (name : String) (aw dw : Nat) :
    List (Expr × String) → Env → Option Env
  | [], env => some env
  | (a, rd) :: rest, env => do
    let av ← evalExpr we env a
    comboReads we mems name aw dw rest
      (fun n => if n = rd then mask dw (mems name (mask aw av)) else env n)

def evalAssigns (we : WEnv) (mems : MEnv) : List Stmt → Env → Option Env
  | [], env => some env
  | .assign l r :: rest, env => do
    let v ← evalExpr we env r
    evalAssigns we mems rest (fun n => if n = l then v else env n)
  | .register _ _ _ _ _ :: rest, env => evalAssigns we mems rest env
  | .memory name aw dw _ _ _ _ ra rd cr _ er :: rest, env =>
    if cr then do
      let env' ← comboReads we mems name aw dw ((ra, rd) :: er) env
      evalAssigns we mems rest env'
    else
      -- sync-read data is register-like state, seeded into env0
      evalAssigns we mems rest env
  | .inst _ _ _ :: rest, env =>
    -- open-module view: instance outputs are free inputs
    evalAssigns we mems rest env

/-- Encode a register's reset value the way `evalExpr` encodes
    constants. -/
def encodeInit (v : Int) (w : Nat) : Nat :=
  mask w (Int.toNat (((v % (2 ^ w : Nat)) + (2 ^ w : Nat)) % (2 ^ w : Nat)))

/-- Synchronous read ports: latch `mem[addr]` (read-old — `mems` is the
    pre-write state) into the register-update list. -/
def syncReadLatches (we : WEnv) (mems : MEnv) (name : String)
    (aw dw : Nat) :
    List (Expr × String) → Env → Option (List (String × Nat))
  | [], _ => some []
  | (a, rd) :: rest, env => do
    let av ← evalExpr we env a
    let latches ← syncReadLatches we mems name aw dw rest env
    some ((rd, mask dw (mems name (mask aw av))) :: latches)

/-- Next values for every register (and sync-read latch), under the
    post-elaboration env. -/
def regNexts (we : WEnv) (mems : MEnv) :
    List Stmt → Env → Option (List (String × Nat))
  | [], _ => some []
  | .register out _ (rstName, _) input init :: rest, env => do
    let vin ← evalExpr we env input
    let nexts ← regNexts we mems rest env
    let next := if env rstName ≠ 0 then encodeInit init (we out)
                else mask (we out) vin
    some ((out, next) :: nexts)
  | .memory name aw dw _ _ _ _ ra rd cr _ er :: rest, env =>
    if cr then regNexts we mems rest env
    else do
      let latches ← syncReadLatches we mems name aw dw ((ra, rd) :: er) env
      let nexts ← regNexts we mems rest env
      some (latches ++ nexts)
  | .assign _ _ :: rest, env => regNexts we mems rest env
  | .inst _ _ _ :: rest, env => regNexts we mems rest env

/-- Write ports of one memory, in port order: an enabled port stores
    `mask dw data` at `mask aw addr`; a later port overwrites an earlier
    one on the same address (the Verilog `always_ff` sequential-`if`
    rule). -/
def memWritePorts (we : WEnv) (env : Env) (name : String) (aw dw : Nat) :
    List (Expr × Expr × Expr) → MEnv → Option MEnv
  | [], m => some m
  | (a, d, en) :: rest, m => do
    let ev ← evalExpr we env en
    let av ← evalExpr we env a
    let dv ← evalExpr we env d
    memWritePorts we env name aw dw rest
      (if ev ≠ 0 then
        (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv
                     else m nm i)
       else m)

/-- Memory state after this cycle's writes, evaluated under the
    post-elaboration env. -/
def memNexts (we : WEnv) : List Stmt → MEnv → Env → Option MEnv
  | [], mems, _ => some mems
  | .memory name aw dw _ wa wd wen _ _ _ ew _ :: rest, mems, env => do
    let mems' ← memWritePorts we env name aw dw ((wa, wd, wen) :: ew) mems
    memNexts we rest mems' env
  | .assign _ _ :: rest, mems, env => memNexts we rest mems env
  | .register _ _ _ _ _ :: rest, mems, env => memNexts we rest mems env
  | .inst _ _ _ :: rest, mems, env => memNexts we rest mems env

/-- One cycle: elaborate, then step the registers.  Returns the final
    combinational environment (outputs are read from it) and the
    register updates. -/
def stepModule (we : WEnv) (body : List Stmt) (env0 : Env)
    (mems : MEnv := fun _ _ => 0) :
    Option (Env × List (String × Nat) × MEnv) := do
  let envF ← evalAssigns we mems body env0
  let nexts ← regNexts we mems body envF
  let mems' ← memNexts we body mems envF
  some (envF, nexts, mems')

section StepGuards
private def weS : WEnv := fun _ => 8
private def envS : Env := fun n =>
  if n == "a" then 0xA5 else if n == "rst" then 0 else if n == "r" then 7 else 0
private def bodyS : List Stmt :=
  [ .assign "w" (.op .add [.ref "a", .ref "r"]),
    .register "r" "clock" ("rst", .asynchronous) (.ref "w") 3 ]
-- combinational: w = a + r = 0xA5 + 7 = 0xAC
#guard (stepModule weS bodyS envS).map (fun p => p.1 "w") = some 0xAC
-- register next: rst=0 → w's value
#guard (stepModule weS bodyS envS).map (fun p => p.2.1) = some [("r", 0xAC)]
-- under reset: init encoded
private def envR : Env := fun n => if n == "rst" then 1 else envS n
#guard (stepModule weS bodyS envR).map (fun p => p.2.1) = some [("r", 3)]
end StepGuards

/-- Width-bounded environment: every name's value fits its width.
    Hardware invariant — inputs are port-width bounded and every write
    the semantics performs is masked.  Recovers the env-dependent
    fragment side conditions (signed-compare value bounds, exact-elide
    range) for module-level use. -/
def Bounded (we : WEnv) (env : Env) : Prop :=
  ∀ n, env n < 2 ^ we n

/-- Apply a register-update list to a state. -/
def applyNexts (st : String → Nat) (nexts : List (String × Nat)) :
    String → Nat :=
  fun n => match nexts.find? (fun p => p.1 == n) with
    | some p => p.2
    | none => st n

/-- Run `k` cycles.  `seed t st` builds cycle `t`'s starting environment
    from the register state (module plumbing — typically inputs overlaid
    on registers — is the CALLER's, so the trace theorem quantifies over
    every seeding discipline).  Returns the per-cycle post-elaboration
    environments, oldest first — the observable trace.  (The cycle
    index passed to `seed` counts DOWN from `k-1`; a caller wanting
    wall-clock indices maps `t ↦ k-1-t`.) -/
def runModule (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) :
    Nat → (String → Nat) → MEnv → Option (List Env)
  | 0, _, _ => some []
  | k + 1, st, mems => do
    let (envF, nexts, mems') ← stepModule we body (seed k st) mems
    let rest ← runModule we body seed k (applyNexts st nexts) mems'
    some (envF :: rest)

-- memory pins: combo read sees PRE-write state (read-old); writes land
-- masked at the masked address; last enabled port wins on collision;
-- sync read latches old data into the register-update list.
private def memBody (combo : Bool) : List Stmt :=
  [ .memory "Mem" 2 8 "clock"
      (.ref "wa") (.ref "wd") (.ref "wen")   -- write port 0
      (.ref "ra") "rdata" combo
      [(.ref "wa2", .ref "wd2", .ref "wen2")]  -- extra write port
      [] ]
private def memEnv : Env := fun n =>
  if n == "wa" then 1 else if n == "wd" then 0x51 else
  if n == "wen" then 1 else
  if n == "wa2" then 1 else if n == "wd2" then 0x62 else
  if n == "wen2" then 0 else
  if n == "ra" then 1 else 0
private def mems0 : MEnv := fun nm i =>
  if nm == "Mem" && i == 1 then 0x33 else 0
-- combo read: rdata = old Mem[1] = 0x33 (NOT this cycle's 0x51)
#guard (stepModule (fun _ => 8) (memBody true) memEnv mems0).map
    (fun p => p.1 "rdata") = some 0x33
-- write port 0 enabled, extra port disabled → Mem[1] = 0x51 after tick
#guard (stepModule (fun _ => 8) (memBody true) memEnv mems0).map
    (fun p => p.2.2 "Mem" 1) = some 0x51
-- collision, both enabled: LAST port wins → 0x62
private def memEnv2 : Env := fun n => if n == "wen2" then 1 else memEnv n
#guard (stepModule (fun _ => 8) (memBody true) memEnv2 mems0).map
    (fun p => p.2.2 "Mem" 1) = some 0x62
-- sync read: rdata latches old Mem[1] into the update list
#guard (stepModule (fun _ => 8) (memBody false) memEnv mems0).map
    (fun p => p.2.1) = some [("rdata", 0x33)]
-- masking: address masked to aw bits, data masked to dw bits
private def memEnvM : Env := fun n =>
  if n == "wa" then 5 else if n == "wd" then 0x151 else memEnv n
#guard (stepModule (fun _ => 8) (memBody true) memEnvM mems0).map
    (fun p => p.2.2 "Mem" 1) = some 0x51

-- multi-cycle: seed each cycle from register state with a=1, rst=0;
-- r accumulates 7, 8, 9 → trace of w = r+1 each cycle
private def seedS : Nat → (String → Nat) → Env := fun _ st n =>
  if n == "a" then 1 else if n == "rst" then 0 else st n
#guard (runModule weS bodyS seedS 3 (fun n => if n == "r" then 7 else 0)
    (fun _ _ => 0)).map
    (fun tr => tr.map (fun e => e "w")) = some [8, 9, 10]

/- Behavioral pins: the semantics agrees with hardware intuition on
   small cases (evaluated at compile time). -/
section Guards
private def we0 : WEnv := fun _ => 8
private def env0 : Env := fun n => if n == "a" then 0xA5 else 0x3C
#guard evalExpr we0 env0 (.op .and [.ref "a", .ref "b"]) = some 0x24
#guard evalExpr we0 env0 (.op .add [.ref "a", .ref "b"]) = some 0xE1
-- 8-bit overflow wraps: 0xA5 + 0xA5 = 0x14A → 0x4A
#guard evalExpr we0 env0 (.op .add [.ref "a", .ref "a"]) = some 0x4A
-- NOT is width-bounded (the emitter bug class, at the semantics level)
#guard evalExpr we0 env0 (.op .not [.ref "a"]) = some 0x5A
-- concat is MSB-first; slice picks the middle byte back out
#guard evalExpr we0 env0 (.concat [.ref "a", .ref "b"]) = some 0xA53C
#guard evalExpr we0 env0 (.slice (.concat [.ref "a", .ref "b"]) 15 8) = some 0xA5
-- mux takes the else arm on 0
#guard evalExpr we0 env0 (.op .mux [.const 0 1, .ref "a", .ref "b"]) = some 0x3C
end Guards

end Sparkle.IR.Semantics
