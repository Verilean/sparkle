/-
  SMT bridge, M1: SMT-LIB2 emission + bounded model checking.
  Design and trust architecture: docs/SmtBridge-design.md.

  The solver is a *finder*, never a trusted authority: `sat` results carry a
  counterexample that the test driver replays on the CSim C reference (a
  false positive from a solver bug OR an emitter bug fails the replay);
  `unsat` is a bounded proof up to k in M1 (kernel-checked certification of
  unbounded invariants is M4).

  Encoding: transition-system frames.  All symbols are |quoted|.  Width
  discipline mirrors CSim's C-promotion+mask semantics: ring ops emit
  operands directly at the target width (truncation commutes); comparisons,
  shr/asr, slice and concat evaluate at natural width first, then coerce.
  Memories become SMT arrays in the array+bit-vector fragment (emitted under
  `ALL` for packaged-Z3 compatibility) — the capability `bv_decide` cannot
  offer. comboRead reads pre-write (CSim eval), sync read is a state var
  latched from the post-write array (CSim tick order).  Reset mirrors CSim:
  frame 0 IS the post-reset state; the `rst` port is an ordinary input.
-/
import Sparkle.Backend.CSim
import Sparkle.IR.Specialize

namespace Sparkle.Backend.Smt

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CSim

/-! ### Symbols and constants -/

/-- Frame-local symbol: `|<sanitized>_c<frame>|` (piped to dodge SMT keywords). -/
private def sym (name : String) (frame : Nat) : String :=
  s!"|{sanitizeName name}_c{frame}|"

private def bvSort (w : Nat) : String := s!"(_ BitVec {w})"

private def bvConst (v : Int) (w : Nat) : String :=
  let m : Int := Int.ofNat (2 ^ w)
  let x := ((v % m) + m) % m
  s!"(_ bv{x.toNat} {w})"

/-- Zero-extend / truncate a term from width `src` to width `dst`. -/
private def coerce (t : String) (src dst : Nat) : String :=
  if src == dst then t
  else if src < dst then s!"((_ zero_extend {dst - src}) {t})"
  else s!"((_ extract {dst - 1} 0) {t})"

/-! ### Memory bookkeeping -/

/-- One `.memory` statement, as the emitter needs it. -/
structure MemInfo where
  name      : String
  addrW     : Nat
  dataW     : Nat
  writeAddr : Expr
  writeData : Expr
  writeEn   : Expr
  readAddr  : Expr
  readData  : String
  comboRead : Bool

private def memsOf (m : Module) : List MemInfo :=
  m.body.filterMap fun s => match s with
    | .memory name aw dw _clk wa wd we ra rd cr =>
      some { name, addrW := aw, dataW := dw, writeAddr := wa, writeData := wd
           , writeEn := we, readAddr := ra, readData := rd, comboRead := cr }
    | _ => none

/-- Build the shared width environment used by validation and emission.
    Memory names are represented as arrays so nested memory selects retain
    their declared data width instead of falling back to 32 bits. -/
private def buildSmtTypeMap (m : Module) : TypeMap :=
  (memsOf m).foldl (fun acc memory =>
    acc.insertIfNew memory.name (.array 1 (.bitVector memory.dataW))) (buildTypeMap m)

/-! ### Expression emission -/

structure Ctx where
  typeMap : TypeMap
  mems    : List MemInfo
  frame   : Nat

/-- Emit `e` coerced to exactly `w` bits, reading frame-`ctx.frame` symbols.

    Ring ops (add/sub/mul/bitwise/shl, mux branches, not/neg) emit operands
    directly at `w` — truncation commutes with them, matching CSim's
    compute-wide-then-mask.  Comparisons, shr/asr, slice, concat and memory
    selects evaluate at natural width first, then coerce. -/
partial def emitW (ctx : Ctx) (e : Expr) (w : Nat) : Except String String := do
  let natW := inferExprWidth ctx.typeMap
  match e with
  | .const v _ => return bvConst v w
  | .ref n =>
    let dw := lookupWidth ctx.typeMap n
    return coerce (sym n ctx.frame) dw w
  | .op .mux [c, t, f] =>
    let cw := max (natW c) 1
    let cs ← emitW ctx c cw
    let ts ← emitW ctx t w
    let fs ← emitW ctx f w
    return s!"(ite (= {cs} {bvConst 0 cw}) {fs} {ts})"
  | .op .not [a] => return s!"(bvnot {← emitW ctx a w})"
  | .op .neg [a] => return s!"(bvneg {← emitW ctx a w})"
  | .op .add [a, b] => return s!"(bvadd {← emitW ctx a w} {← emitW ctx b w})"
  | .op .sub [a, b] => return s!"(bvsub {← emitW ctx a w} {← emitW ctx b w})"
  | .op .mul [a, b] => return s!"(bvmul {← emitW ctx a w} {← emitW ctx b w})"
  | .op .and [a, b] => return s!"(bvand {← emitW ctx a w} {← emitW ctx b w})"
  | .op .or  [a, b] => return s!"(bvor {← emitW ctx a w} {← emitW ctx b w})"
  | .op .xor [a, b] => return s!"(bvxor {← emitW ctx a w} {← emitW ctx b w})"
  | .op .shl [a, b] => return s!"(bvshl {← emitW ctx a w} {← emitW ctx b w})"
  | .op .shr [a, b] =>
    -- High bits of `a` matter: evaluate at natural width, then coerce.
    let wa := max (natW a) 1
    let r := s!"(bvlshr {← emitW ctx a wa} {← emitW ctx b wa})"
    return coerce r wa w
  | .op .asr [a, b] =>
    let wa := max (natW a) 1
    let r := s!"(bvashr {← emitW ctx a wa} {← emitW ctx b wa})"
    return coerce r wa w
  | .op cmp [a, b] =>
    -- Comparisons: natural common width, 1-bit result, coerce up if needed.
    let pred? : Option String := match cmp with
      | .eq => some "="     | .lt_u => some "bvult" | .lt_s => some "bvslt"
      | .le_u => some "bvule" | .le_s => some "bvsle" | .gt_u => some "bvugt"
      | .gt_s => some "bvsgt" | .ge_u => some "bvuge" | .ge_s => some "bvsge"
      | _ => none
    match pred? with
    | some pred =>
      let wm := max (max (natW a) (natW b)) 1
      let as_ ← emitW ctx a wm
      let bs ← emitW ctx b wm
      return coerce s!"(ite ({pred} {as_} {bs}) #b1 #b0)" 1 w
    | none => throw s!"unsupported operator arity/shape: {e}"
  | .concat args =>
    if args.isEmpty then return bvConst 0 w
    let parts ← args.mapM (fun a => do
      let wa := max (natW a) 1
      return (← emitW ctx a wa, wa))
    let total := parts.foldl (fun acc p => acc + p.2) 0
    let joined := match parts.map (·.1) with
      | [single] => single
      | many => s!"(concat {String.intercalate " " many})"
    return coerce joined total w
  | .slice inner hi lo =>
    let wi := max (natW inner) 1
    let s ← emitW ctx inner wi
    if hi ≥ wi || lo > hi then
      throw s!"slice [{hi}:{lo}] out of range for width {wi}: {e}"
    return coerce s!"((_ extract {hi} {lo}) {s})" (hi - lo + 1) w
  | .sliceDim _ hi lo =>
    throw s!"SMT backend requires concrete slice bounds; found symbolic slice [{hi}:{lo}]. Specialize retained parameters before SMT emission"
  | .index (.ref arr) idx =>
    match ctx.mems.find? (·.name == arr) with
    | some mi =>
      let idxS ← emitW ctx idx mi.addrW
      return coerce s!"(select {sym mi.name ctx.frame} {idxS})" mi.dataW w
    | none => throw s!"'.index' on '{arr}' — only memory selects are supported in v1"
  | _ => throw s!"unsupported expression in SMT emission: {e}"

/-! ### Transition-system extraction and frame emission -/

private structure RegInfo where
  name  : String
  width : Nat
  init  : Int
  input : Expr

private def regsOf (m : Module) (tm : TypeMap) : List RegInfo :=
  m.body.filterMap fun s => match s with
    | .register out _ _ input init =>
      some { name := out, width := lookupWidth tm out, init, input }
    | _ => none

/-- Non-clk input ports (rst included — an ordinary input under CSim
    semantics; reset is frame 0's initial state). -/
def bmcInputs (m : Module) : List Port :=
  m.inputs.filter (·.name != "clk")

/-- Sanity checks + collected pieces for the frame emitter. -/
private def checkModule (m : Module) : Except String Unit := do
  if !m.parameters.isEmpty then
    throw s!"module '{m.name}' has retained symbolic parameters; the SMT backend requires an explicitly specialized concrete module"
  for p in m.inputs ++ m.outputs ++ m.wires do
    match p.ty.bitWidth? with
    | some 0 =>
      throw s!"{p.name}: the SMT backend requires a positive concrete bit width; zero-width ports and wires are not valid SMT bit-vectors"
    | some _ => pure ()
    | none =>
      throw s!"{p.name}: the SMT backend requires a concrete bit width; specialize retained parameters before SMT emission"
  for s in m.body do
    match s with
    | .inst _ instName _ =>
      throw s!"instance '{instName}': the SMT backend takes FLAT modules in v1 — flatten the hierarchy first (the elaborator inlines by default)"
    | .memory name addrWidth dataWidth .. =>
      if addrWidth == 0 then
        throw s!"memory '{name}': the SMT backend requires a positive address width"
      if dataWidth == 0 then
        throw s!"memory '{name}': the SMT backend requires a positive data width"
    | _ => pure ()
  if m.assertions.isEmpty then
    throw s!"module '{m.name}' has no assertions — nothing to check (fill Module.assertions)"
  let typeMap := buildSmtTypeMap m
  for (name, expression) in m.assertions do
    let width := inferExprWidth typeMap expression
    if width != 1 then
      throw s!"assertion '{name}' has width {width}; SMT assertions must be exactly 1 bit"

/-- Emit one frame: wire defines (body order), memory reads, register /
    memory next-state defines (into frame c+1), assertion defines. -/
private def emitFrame (m : Module) (tm : TypeMap) (mems : List MemInfo)
    (c : Nat) : Except String (List String) := do
  let ctx : Ctx := { typeMap := tm, mems, frame := c }
  let mut lines : List String := [s!"; ── frame {c} ──"]
  -- inputs
  for p in bmcInputs m do
    lines := lines ++ [s!"(declare-const {sym p.name c} {bvSort p.ty.bitWidth})"]
  -- body in order: assigns, register next-states, and memories each at
  -- their own position (a later assign may read a memory's rd — SMT
  -- define-fun requires definition-before-use, so order matters).
  for s in m.body do
    match s with
    | .assign lhs rhs =>
      let w := lookupWidth tm lhs
      lines := lines ++
        [s!"(define-fun {sym lhs c} () {bvSort w} {← emitW ctx rhs w})"]
    | .register out _ _ input _ =>
      let w := lookupWidth tm out
      lines := lines ++
        [s!"(define-fun {sym out (c+1)} () {bvSort w} {← emitW ctx input w})"]
    | .memory name aw dw _clk wa wd we ra rd cr =>
      let waS ← emitW ctx wa aw
      let wdS ← emitW ctx wd dw
      let weW := max (inferExprWidth tm we) 1
      let weS ← emitW ctx we weW
      let raS ← emitW ctx ra aw
      let arrSort := s!"(Array {bvSort aw} {bvSort dw})"
      if cr then
        -- comboRead: reads the PRE-write array (CSim eval order)
        lines := lines ++
          [s!"(define-fun {sym rd c} () {bvSort dw} (select {sym name c} {raS}))"]
      lines := lines ++
        [s!"(define-fun {sym name (c+1)} () {arrSort} (ite (= {weS} {bvConst 0 weW}) {sym name c} (store {sym name c} {waS} {wdS})))"]
      if !cr then
        -- sync read: registered, reads the POST-write array (CSim tick order)
        lines := lines ++
          [s!"(define-fun {sym rd (c+1)} () {bvSort dw} (select {sym name (c+1)} {raS}))"]
    | .inst .. => pure ()  -- rejected earlier
  -- assertions (1-bit; violated when = 0)
  for (aname, aexpr) in m.assertions do
    lines := lines ++
      [s!"(define-fun {sym s!"_assert_{aname}" c} () {bvSort 1} {← emitW ctx aexpr 1})"]
  return lines

/-- Full BMC query: frames 0..k, property violation disjunction, check-sat,
    get-value over every input of every frame. -/
def toSmtBmcQuery (m : Module) (k : Nat) : Except String String := do
  checkModule m
  let tm := buildSmtTypeMap m
  let mems := memsOf m
  let regs := regsOf m tm
  -- Ubuntu's packaged Z3 rejects constant-array terms under QF_ABV even
  -- though the terms are valid SMT-LIB. ALL keeps the same quantifier-free
  -- array/bit-vector query accepted across the supported Z3 versions.
  let logic := if mems.isEmpty then "QF_BV" else "ALL"
  let mut lines : List String :=
    [ s!"; AUTO-GENERATED by Sparkle HDL — SMT bridge (BMC, k={k})"
    , s!"; module {m.name}; semantics mirror the CSim reference (see docs/SmtBridge-design.md)"
    , "(set-option :produce-models true)"
    , s!"(set-logic {logic})"
    , "; ── frame 0: post-reset state ──" ]
  for r in regs do
    lines := lines ++
      [s!"(define-fun {sym r.name 0} () {bvSort r.width} {bvConst r.init r.width})"]
  for mi in mems do
    let arrSort := s!"(Array {bvSort mi.addrW} {bvSort mi.dataW})"
    lines := lines ++
      [s!"(define-fun {sym mi.name 0} () {arrSort} ((as const {arrSort}) {bvConst 0 mi.dataW}))"]
    if !mi.comboRead then
      lines := lines ++
        [s!"(define-fun {sym mi.readData 0} () {bvSort mi.dataW} {bvConst 0 mi.dataW})"]
  for c in [0:k+1] do
    lines := lines ++ (← emitFrame m tm mems c)
  -- violation disjunction over every assertion at every frame
  let mut viols : List String := []
  for c in [0:k+1] do
    for (aname, _) in m.assertions do
      viols := viols ++ [s!"(= {sym s!"_assert_{aname}" c} #b0)"]
  lines := lines ++
    [ "; ── property: some assertion is violated within k cycles ──"
    , s!"(assert (or {String.intercalate " " viols}))"
    , "(check-sat)" ]
  -- model extraction: all inputs, all frames
  let mut vals : List String := []
  for c in [0:k+1] do
    for p in bmcInputs m do
      vals := vals ++ [sym p.name c]
  lines := lines ++ [s!"(get-value ({String.intercalate " " vals}))"]
  return String.intercalate "\n" lines ++ "\n"


/-- Specialize every retained hardware dimension for one explicit
    configuration, then emit a concrete SMT-LIB2 bounded-model-checking
    query.

    This deliberately does not run the generic IR optimizer between
    specialization and emission. The current optimizer does not yet treat
    `Module.assertions` as reachability roots or rewrite them during CSE, so
    optimizing here could remove or rename logic used only by a property. -/
def toSmtBmcQueryWithParameters (m : Module)
    (bindings : Sparkle.IR.Specialize.Bindings) (k : Nat) :
    Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeModule m bindings
  toSmtBmcQuery concrete k

/-! ### Solver-output parsing -/

/-- Outcome of a BMC run.  `sat` carries per-frame input assignments:
    `cex[c]` lists `(inputName, value)` for frame `c` (missing inputs are
    solver don't-cares — replay uses 0). -/
inductive BmcOutcome where
  | unsat
  | unknown
  | sat (cex : Array (List (String × Nat)))
  deriving Repr

private def tokenize (s : String) : List String :=
  let s := s.replace "(" " ( " |>.replace ")" " ) "
  (s.splitOn " ").flatMap (fun t =>
    let t := t.trim
    if t.isEmpty then [] else [t])

private def parseBvToken (t : String) : Option Nat :=
  if t.startsWith "#b" then
    (t.drop 2).foldl (fun acc c => acc.bind (fun n =>
      if c == '0' then some (2*n) else if c == '1' then some (2*n+1) else none))
      (some 0)
  else if t.startsWith "#x" then
    (t.drop 2).foldl (fun acc c => acc.bind (fun n =>
      let d := if c.isDigit then some (c.toNat - '0'.toNat)
               else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
               else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
               else none
      d.map (fun d => 16*n + d))) (some 0)
  else none

/-- Strip the `|...|` quoting and the `_c<frame>` suffix.
    Returns (baseName, frame). -/
private def splitSym (t : String) : Option (String × Nat) :=
  let t := if t.startsWith "|" && t.endsWith "|" then ((t.drop 1).dropRight 1).toString else t
  match t.splitOn "_c" with
  | [] | [_] => none
  | parts =>
    let frameS := parts.getLast!
    let base := String.intercalate "_c" (parts.dropLast)
    frameS.toNat?.map (fun f => (base, f))

/-- Parse z3 stdout: `sat`/`unsat`/`unknown`, then (for sat) the get-value
    association list.  Handles `#b…`, `#x…` and `(_ bvN w)` value forms. -/
partial def parseZ3Output (out : String) (k : Nat) : Except String BmcOutcome := do
  let toks := tokenize out
  match toks.head? with
  | some "unsat" => return .unsat
  | some "unknown" => return .unknown
  | some "sat" =>
    let mut cex : Array (List (String × Nat)) := Array.replicate (k+1) []
    let mut rest := toks.tail!
    -- Scan for `|name_c<frame>|` symbols; the tokens right after each one
    -- form its value (`#b…`, `#x…`, or `( _ bvN w )`).  Everything else —
    -- parens, stray tokens — is skipped, so the exact get-value nesting
    -- shape doesn't matter.
    while !rest.isEmpty do
      match rest with
      | nameTok :: more =>
        if nameTok.startsWith "|" then
          match splitSym nameTok with
          | some (base, frame) =>
            let (val?, more') : Option Nat × List String :=
              match more with
              | "(" :: "_" :: bv :: _w :: ")" :: tl =>
                (if bv.startsWith "bv" then ((bv.drop 2).toString.toNat?) else none, tl)
              | v :: tl => (parseBvToken v, tl)
              | [] => (none, [])
            match val? with
            | some v =>
              if frame ≤ k then
                cex := cex.modify frame (fun l => l ++ [(base, v)])
            | none => pure ()
            rest := more'
          | none => rest := more
        else
          rest := more
      | [] => pure ()
    return .sat cex
  | _ => throw s!"unrecognised solver output: {out.take 200}"

/-! ### Replay support — assertions as observable outputs -/

/-- A copy of `m` whose assertions are exported as extra 1-bit OUTPUT ports
    (`_assert_<name>`), so the CSim replay can observe them as struct fields
    (internal wires may be eval-locals). -/
def withAssertOutputs (m : Module) : Module :=
  let extraOuts := m.assertions.map fun (n, _) =>
    (⟨s!"_assert_{n}", .bitVector 1⟩ : Port)
  let extraAssigns := m.assertions.map fun (n, e) =>
    (.assign s!"_assert_{n}" e : Stmt)
  { m with outputs := m.outputs ++ extraOuts
         , body := m.body ++ extraAssigns }

end Sparkle.Backend.Smt
