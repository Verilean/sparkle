/-
  IR → circuit-DSL decompiler + `#verify_dsl_roundtrip`.

  `#verify_emit` (VerifyEmit.lean) closes lean₄ → IR → Verilog → IR'.
  This module closes the OTHER loop the toolchain was missing:

      lean₄ (circuit do)
        --synthesize-->  IR design D
        --toCircuitDsl-> Lean SOURCE TEXT (circuit do, Signal.reg, <~)
        --elab in place-> a fresh definition
        --synthesize-->  IR design D'
        --bv_decide----> per-register / per-output cone theorems D ≡ D'

  `toCircuitDsl` is also the seed of "transpile ingested Verilog into
  MAINTAINABLE Sparkle source": any IR within its supported shape —
  whether it came from the DSL or from the SystemVerilog front-end —
  prints as an ordinary `Signal.circuit do` definition.

  v1 scope: single module, exactly one output, no memories or
  sub-instances, operator subset {const, ref, add, sub, mul, and, or,
  xor, not, concat, slice, shl/shr by constant, mux with a 1-bit
  condition}.  Unsupported shapes fail with a named error.

  Name discipline: the elaborator prefixes DSL inputs with `_gen_` and
  invents `_tmp_*` register names, so the roundtripped design's names
  never match the original's.  Inputs are matched by the stripped
  parameter name; registers are matched positionally (width + init +
  reset checked); the reparsed cones are α-renamed back onto the
  original names before the bv_decide comparison.
-/

import Lean
import Tools.SVParser.VerifyEmit

namespace Tools.SVParser.DslEmit

open Lean Elab Command
open Sparkle.IR.AST
open Tools.SVParser.VerifyEmit

/-- Parameter name for an IR input: strip the elaborator's `_gen_`
    prefix so re-synthesis reproduces the same input name. -/
def paramName (n : String) : String :=
  let base := if n.startsWith "_gen_" then n.drop 5 |>.toString else n
  Sparkle.Backend.Verilog.sanitizeName base

/-- Signal-level variable text for an input/register reference.

    A `let r ← Signal.reg …` binder has type `Reg dom …`, which coerces
    to `Signal dom τ` only when unification asks for it — `.map`, `++`
    and `Signal.ult` all see the `Reg` first and fail to elaborate.  So
    every register READ is printed with an explicit ascription; `<~`
    still takes the bare binder on the left. -/
private def refText (wt : Std.HashMap String Nat)
    (regNames : List (String × String)) (n : String) : String :=
  match regNames.find? (·.1 == n) with
  | some (_, dslName) =>
    match wt.get? n with
    | some w => s!"({dslName} : Signal defaultDomain (BitVec {w}))"
    | none => dslName
  | none => paramName n

/-- Widths for concat members, used by `simplifyCone`. -/
private partial def wOf (wt : Std.HashMap String Nat) :
    Sparkle.IR.AST.Expr → Option Nat
  | .const _ w => some w
  | .ref n => wt.get? n
  | .slice _ hi lo => some (hi - lo + 1)
  | .concat args => args.foldl (fun acc a =>
      match acc, wOf wt a with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0)
  | .op op args =>
    match op, args with
    | .eq, _ | .lt_u, _ | .lt_s, _ | .le_u, _ | .le_s, _
    | .gt_u, _ | .gt_s, _ | .ge_u, _ | .ge_s, _ => some 1
    | .mux, [_, t, _] => wOf wt t
    | _, a :: _ => wOf wt a
    | _, [] => none
  | _ => none

/-- Normalize the shapes `circuit do` lowering leaves behind:

    * 0-width members inside a `concat` (degenerate HList tails);
    * `concat [r0, r1, …][hi:lo]` selecting exactly ONE member — the
      register bundle read — collapses to that member;
    * `concat [x]` collapses to `x`;
    * a full-width slice of a known-width expression is the identity.

    Without this the decompiled source names the whole register bundle
    (`r0 ++ r1 ++ …`)[hi,lo] instead of `r1`, which does not even
    typecheck in the DSL (`Reg` has no `HAppend`). -/
private partial def simplifyCone (wt : Std.HashMap String Nat) :
    Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .concat args =>
    let args := (args.map (simplifyCone wt)).filter fun a =>
      match wOf wt a with | some 0 => false | _ => true
    match args with
    | [x] => x
    | _ => .concat args
  | .slice e hi lo =>
    let e := simplifyCone wt e
    match e with
    | .concat args =>
      -- MSB-first layout: walk members from the top, find the one that
      -- exactly covers [hi:lo]
      let total := (args.foldl (fun acc a => acc + (wOf wt a).getD 0) 0)
      let rec go (rest : List Sparkle.IR.AST.Expr) (top : Nat) :
          Sparkle.IR.AST.Expr :=
        match rest with
        | [] => .slice e hi lo
        | a :: tl =>
          let w := (wOf wt a).getD 0
          let aHi := top - 1
          let aLo := top - w
          if hi == aHi && lo == aLo then a
          else if hi ≤ aHi && lo ≥ aLo then
            simplifyCone wt (.slice a (hi - aLo) (lo - aLo))
          else go tl aLo
      go args total
    | _ =>
      match wOf wt e with
      | some w => if lo == 0 && hi + 1 == w then e else .slice e hi lo
      | none => .slice e hi lo
  | .op o args => .op o (args.map (simplifyCone wt))
  | .index a i => .index (simplifyCone wt a) (simplifyCone wt i)
  | e => e

mutual

/-- Render an inlined IR expression (refs are inputs/registers only) as
    circuit-DSL source text.  Mutually recursive with `cmpOperand`, which
    brings two operands of a width-polymorphic IR node to one width. -/
partial def dslExpr (wt : Std.HashMap String Nat)
    (regNames : List (String × String)) :
    Sparkle.IR.AST.Expr → Except String String
  | .const v w =>
    if v < 0 then
      let m : Int := (2 : Int) ^ w
      .ok s!"(Signal.pure ({((v % m + m) % m)}#{w}) : Signal defaultDomain (BitVec {w}))"
    else
      .ok s!"(Signal.pure ({v}#{w}) : Signal defaultDomain (BitVec {w}))"
  | .ref n => .ok (refText wt regNames n)
  | .slice e hi lo => do
    -- NOT `x[hi, lo]`: `HasBitSlice.slice` has type
    -- `BitVec (hi - lo + 1)` — a syntactically UNREDUCED width that the
    -- DSL's HAdd/HSub instances reject and that the synth elaborator
    -- cannot inline ("Cannot instantiate HasBitSlice.slice: not a
    -- hardware module definition").  `BitVec.extractLsb' lo w` has a
    -- literal width, and the elaborator maps exactly the LAMBDA form
    -- `.map (fun x => BitVec.extractLsb' …)` to `Expr.slice` — a
    -- partially applied `extractLsb' lo w` is not a lambda and misses
    -- that path.
    .ok s!"(({← dslExpr wt regNames e}).map (fun x => BitVec.extractLsb' {lo} {hi - lo + 1} x))"
  | .concat args => do
    match args with
    | [] => .error "empty concat"
    | a :: rest =>
      let mut acc ← dslExpr wt regNames a
      for r in rest do
        acc := s!"({acc} ++ {← dslExpr wt regNames r})"
      .ok acc
  | .op o args => do
    -- IR binary ops inherit Verilog's context sizing and may mix widths
    -- (`BitVec 4 * BitVec 32`); the width-indexed DSL instances demand
    -- one width, so operands are normalized to the wider one.  Very wide
    -- results are DECLINED rather than printed: zero-extending a small
    -- operand up to e.g. 4096 bits builds `0#4092 ++ …` terms that either
    -- mismatch or exhaust `whnf` heartbeats — "printable" must mean
    -- "elaborates".
    let bin := fun (sym : String) (a b : Sparkle.IR.AST.Expr) => do
      let wa := (widthOf wt a).toOption.getD 1
      let wb := (widthOf wt b).toOption.getD 1
      if wa == wb then
        .ok s!"({← dslExpr wt regNames a} {sym} {← dslExpr wt regNames b})"
      else if max wa wb > 64 then
        .error s!"mixed-width `{sym}` at {max wa wb} bits not in the v1 circuit-DSL subset"
      else
        let w := max wa wb
        .ok s!"({← cmpOperand wt regNames w a} {sym} {← cmpOperand wt regNames w b})"
    match o, args with
    | .add, [a, b] => bin "+" a b
    | .sub, [a, b] => bin "-" a b
    | .mul, [a, b] => bin "*" a b
    | .and, [a, b] => bin "&&&" a b
    | .or,  [a, b] => bin "|||" a b
    | .xor, [a, b] => bin "^^^" a b
    | .not, [a] => do
      -- no synthesizable Complement instance: ~x ≡ x ^^^ all-ones
      let w ← widthOf wt a
      let ones : Nat := (1 <<< w) - 1
      .ok s!"({← dslExpr wt regNames a} ^^^ ({ones}#{w} : BitVec {w}))"
    | .shl, [a, .const v _] => do
      let w ← widthOf wt a
      .ok s!"({← dslExpr wt regNames a} <<< ({v}#{w} : BitVec {w}))"
    | .shr, [a, .const v _] => do
      let w ← widthOf wt a
      .ok s!"({← dslExpr wt regNames a} >>> ({v}#{w} : BitVec {w}))"
    | .shl, [a, b] => do
      -- dynamic amount: value and amount must share a width; a very wide
      -- value would need an absurd zero-extension of the amount, so it is
      -- declined (those shapes are packed-array index computations).
      let wa ← widthOf wt a
      if wa > 64 then
        .error s!"dynamic shift of a {wa}-bit value not in the v1 circuit-DSL subset"
      else
        let amt ← cmpOperand wt regNames wa b
        .ok s!"((Signal.ap (Signal.map (fun (x : BitVec {wa}) (y : BitVec {wa}) => x <<< y) {← cmpOperand wt regNames wa a}) {amt}) : Signal defaultDomain (BitVec {wa}))"
    | .shr, [a, b] => do
      let wa ← widthOf wt a
      if wa > 64 then
        .error s!"dynamic shift of a {wa}-bit value not in the v1 circuit-DSL subset"
      else
        let amt ← cmpOperand wt regNames wa b
        .ok s!"((Signal.ap (Signal.map (fun (x : BitVec {wa}) (y : BitVec {wa}) => x >>> y) {← cmpOperand wt regNames wa a}) {amt}) : Signal defaultDomain (BitVec {wa}))"
    | .lt_u, [a, b] | .le_u, [a, b] | .gt_u, [a, b] | .ge_u, [a, b]
    | .lt_s, [a, b] | .le_s, [a, b] | .gt_s, [a, b] | .ge_s, [a, b] => do
      -- `Signal.{ult,ule,slt,sle}` are Bool-valued; gt/ge are the same
      -- with the operands swapped.  Lift back to BitVec 1 via mux so the
      -- result composes in arithmetic contexts (mux conditions strip it
      -- again below).
      let (fn, x, y) := match o with
        | .lt_u => ("Signal.ult", a, b) | .le_u => ("Signal.ule", a, b)
        | .gt_u => ("Signal.ult", b, a) | .ge_u => ("Signal.ule", b, a)
        | .lt_s => ("Signal.slt", a, b) | .le_s => ("Signal.sle", a, b)
        | .gt_s => ("Signal.slt", b, a) | _      => ("Signal.sle", b, a)
      let w := max ((widthOf wt x).toOption.getD 1) ((widthOf wt y).toOption.getD 1)
      if w > 64 then .error s!"comparison at {w} bits not in the v1 circuit-DSL subset" else
      .ok s!"(Signal.mux ({fn} {← cmpOperand wt regNames w x} {← cmpOperand wt regNames w y}) (Signal.pure (1#1) : Signal defaultDomain (BitVec 1)) (Signal.pure (0#1) : Signal defaultDomain (BitVec 1)))"
    | .eq, [a, b] => do
      -- The elaborator maps `BEq.beq` to `.eq`; a Bool-valued Signal is
      -- what `Signal.mux` wants as its condition, and lifting it back to
      -- BitVec 1 (for arithmetic contexts) uses the same mux.
      let w := max ((widthOf wt a).toOption.getD 1) ((widthOf wt b).toOption.getD 1)
      if w > 64 then .error s!"comparison at {w} bits not in the v1 circuit-DSL subset" else
      .ok s!"(Signal.mux (Signal.ap (Signal.map (· == ·) {← cmpOperand wt regNames w a}) {← cmpOperand wt regNames w b}) (Signal.pure (1#1) : Signal defaultDomain (BitVec 1)) (Signal.pure (0#1) : Signal defaultDomain (BitVec 1)))"
    | .mux, [c, t, e] => do
      let wc ← widthOf wt c
      if wc != 1 then .error s!"mux condition of width {wc} (v1 supports 1-bit)"
      else
        -- Bool-valued condition without a BitVec detour when the cone is
        -- itself a comparison (the common `.map (· == 1#1)` shape).
        let condTxt ← match c with
          | .op .eq [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.ap (Signal.map (· == ·) {← cmpOperand wt regNames w ca}) {← cmpOperand wt regNames w cb})"
          | .op .lt_u [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.ult {← cmpOperand wt regNames w ca} {← cmpOperand wt regNames w cb})"
          | .op .le_u [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.ule {← cmpOperand wt regNames w ca} {← cmpOperand wt regNames w cb})"
          | .op .gt_u [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.ult {← cmpOperand wt regNames w cb} {← cmpOperand wt regNames w ca})"
          | .op .ge_u [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.ule {← cmpOperand wt regNames w cb} {← cmpOperand wt regNames w ca})"
          | .op .lt_s [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.slt {← cmpOperand wt regNames w ca} {← cmpOperand wt regNames w cb})"
          | .op .le_s [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.sle {← cmpOperand wt regNames w ca} {← cmpOperand wt regNames w cb})"
          | .op .gt_s [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.slt {← cmpOperand wt regNames w cb} {← cmpOperand wt regNames w ca})"
          | .op .ge_s [ca, cb] => do
            let w := max ((widthOf wt ca).toOption.getD 1) ((widthOf wt cb).toOption.getD 1)
            if w > 64 then .error s!"mux condition compares {w} bits (v1 limit)" else
            .ok s!"(Signal.sle {← cmpOperand wt regNames w cb} {← cmpOperand wt regNames w ca})"
          | _ =>
            -- any other 1-bit cone (a slice, a wire, an and/or tree):
            -- lift to Bool.  Parenthesize so `[hi, lo]` binds first.
            .ok s!"(({← dslExpr wt regNames c}).map (· == 1#1))"
        .ok s!"(Signal.mux {condTxt} {← dslExpr wt regNames t} {← dslExpr wt regNames e})"
    | _, _ => .error s!"operator {repr o}/{args.length} not in the v1 circuit-DSL subset"
  | e => .error s!"expression {repr e} not in the v1 circuit-DSL subset"

/-- Render an operand at a common width `w`: constants are
    re-materialised at `w`, narrower expressions zero-extended, wider
    ones truncated.  IR nodes inherit Verilog's context sizing
    (`x == 32'd0` against a 4-bit `x`), which the width-indexed DSL will
    not accept. -/
partial def cmpOperand (wt : Std.HashMap String Nat)
    (regNames : List (String × String)) (w : Nat)
    (e : Sparkle.IR.AST.Expr) : Except String String := do
  match e with
  | .const v _ =>
    let m : Int := (2 : Int) ^ w
    let uv := ((v % m) + m) % m
    .ok s!"(Signal.pure ({uv}#{w}) : Signal defaultDomain (BitVec {w}))"
  | _ =>
    let we ← widthOf wt e
    let txt ← dslExpr wt regNames e
    if we == w then .ok s!"(({txt} : Signal defaultDomain (BitVec {w})))"
    else if we < w then
      .ok s!"(((Signal.pure (0#{w - we}) : Signal defaultDomain (BitVec {w - we})) ++ {txt}) : Signal defaultDomain (BitVec {w}))"
    else
      .ok s!"((({txt}).map (fun x => BitVec.extractLsb' 0 {w} x)) : Signal defaultDomain (BitVec {w}))"

end


/-- Rewrite a reparsed register cone into its rst = 0 form: replace
    every `.ref rstName` with 0, then constant-fold the muxes it feeds.
    firtool's emitted `always_ff` puts the reset branch INSIDE the data
    expression (`mux(¬rst & c, v, mux(rst, init, hold))`); in the DSL the
    reset lives in `Signal.reg` instead, so the printed source must not
    mention it (there is no `reset` binder in scope). -/
partial def dropReset (rstNames : List String) :
    Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .ref n => if rstNames.contains n then .const 0 1 else .ref n
  | .op o args =>
    let args := args.map (dropReset rstNames)
    match o, args with
    -- constant-fold once the reset ref became 0
    | .and, [.const 0 _, _] | .and, [_, .const 0 _] => .const 0 1
    | .and, [.const _ _, x] => x
    | .and, [x, .const v _] => if v == 0 then .const 0 1 else x
    | .or,  [.const 0 _, x] => x
    | .or,  [x, .const 0 _] => x
    | .xor, [.const 0 _, x] => x
    | .xor, [x, .const 0 _] => x
    | .not, [.const 0 w] => .const ((1 <<< w) - 1) w
    | .mux, [.const 0 _, _, e] => e
    | .mux, [.const _ _, t, _] => t
    | _, _ => .op o args
  | .concat args => .concat (args.map (dropReset rstNames))
  | .slice e hi lo => .slice (dropReset rstNames e) hi lo
  | .index a i => .index (dropReset rstNames a) (dropReset rstNames i)
  | e => e

/-- Decompile a single-output IR module to a `circuit do` definition.
    Returns (source text, register order used). -/
def toCircuitDsl (m : Sparkle.IR.AST.Module) (defName : String) :
    Except String (String × List String) := do
  if m.body.any (fun s => match s with | .inst .. => true | _ => false) then
    .error "sub-instances unsupported (v1)"
  else if m.body.any (fun s => match s with | .memory .. => true | _ => false) then
    .error "memories unsupported (v1)"
  else
  let [out] := m.outputs
    | .error s!"v1 needs exactly one output (got {m.outputs.length})"
  let wt := widthTable m
  let sigs := regSigs m
  let (regCones, outCones) ← conesOf m
  let some outCone := (outCones.find? (·.1 == out.name)).map (·.2)
    | .error "output cone missing"
  -- DSL-side register names r0, r1, … in body order
  let regNames : List (String × String) :=
    (sigs.zipIdx).map (fun ((n, _, _, _), i) => (n, s!"r{i}"))
  let rstUsed := (sigs.map (fun (_, _, _, r) => r)).eraseDups
  let dataIns := m.inputs.filter fun p =>
    !isClockName p.name && p.name != "rst" && p.name != "reset"
      && !rstUsed.contains p.name
  let params := String.intercalate " " (dataIns.map fun p =>
    s!"({paramName p.name} : Signal defaultDomain (BitVec {p.ty.bitWidth}))")
  let rstNames := (sigs.map (fun (_, _, _, r) => r)).eraseDups
  let prep := fun (e : Sparkle.IR.AST.Expr) =>
    simplifyCone wt (dropReset rstNames e)
  let mut lines : List String := []
  if sigs.isEmpty then
    -- purely combinational: `circuit do` requires at least one register
    lines := lines ++
      [s!"def {defName} {params} : Signal defaultDomain (BitVec {out.ty.bitWidth}) :="
      , s!"  {← dslExpr wt regNames (prep outCone)}"]
  else
    lines := lines ++
      [s!"def {defName} {params} : Signal defaultDomain (BitVec {out.ty.bitWidth}) :="
      , "  circuit do"]
    for ((n, w, init, _), i) in sigs.zipIdx do
      let _ := n
      lines := lines ++ [s!"    let r{i} ← Signal.reg ({init}#{w})"]
    for (n, cone) in regCones do
      let some (_, dslName) := regNames.find? (·.1 == n)
        | .error s!"register {n} missing from name table"
      lines := lines ++ [s!"    {dslName} <~ {← dslExpr wt regNames (prep cone)}"]
    lines := lines ++ [s!"    return {← dslExpr wt regNames (prep outCone)}"]
  .ok (String.intercalate "\n" lines, regNames.map (·.1))

/-- α-rename input/register refs of the REPARSED design's cones back to
    the ORIGINAL design's names, so both sides share one binder set. -/
partial def renameRefs (map : Std.HashMap String String) :
    Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .ref n => .ref (map.getD n n)
  | .op o args => .op o (args.map (renameRefs map))
  | .concat args => .concat (args.map (renameRefs map))
  | .slice e hi lo => .slice (renameRefs map e) hi lo
  | .index a i => .index (renameRefs map a) (renameRefs map i)
  | e => e

syntax (name := verifyDslRoundtripCmd) "#verify_dsl_roundtrip " ident : command

@[command_elab verifyDslRoundtripCmd]
def elabVerifyDslRoundtrip : CommandElab := fun stx => do
  match stx with
  | `(#verify_dsl_roundtrip $f:ident) => do
    let declName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
    let design ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
    let some m := design.modules.head?
      | throwErrorAt f "#verify_dsl_roundtrip: empty design"
    if design.modules.length != 1 then
      throwErrorAt f "#verify_dsl_roundtrip: hierarchical designs unsupported (v1)"
    -- 1. decompile to circuit-DSL source
    let rtName := s!"{f.getId.eraseMacroScopes.toString.replace "." "_"}_dslRT"
    let (src, regOrder) ← match toCircuitDsl m rtName with
      | .ok r => pure r
      | .error e => throwErrorAt f "#verify_dsl_roundtrip: {e}"
    logInfoAt stx m!"generated circuit-DSL source:\n{src}"
    -- 2. elaborate the generated definition IN PLACE
    let env ← getEnv
    let cmdStx ← match Lean.Parser.runParserCategory env `command src with
      | .ok s => pure s
      | .error e => throwErrorAt f "#verify_dsl_roundtrip: generated source does not parse: {e}"
    elabCommand cmdStx
    -- 3. re-synthesize the generated definition
    let rtDecl ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdent (Name.mkSimple rtName)))
    let design' ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical rtDecl)
    let some m' := design'.modules.head?
      | throwErrorAt f "#verify_dsl_roundtrip: re-synthesis produced no module"
    -- 4. structural checks + name mapping (rt name → original name)
    let sigL := regSigs m
    let sigR := regSigs m'
    unless sigL.length == sigR.length do
      throwErrorAt f "#verify_dsl_roundtrip: register count changed ({sigL.length} → {sigR.length})"
    for ((_, wL, iL, _), (_, wR, iR, _)) in sigL.zip sigR do
      unless wL == wR && iL == iR do
        throwErrorAt f "#verify_dsl_roundtrip: register width/init mismatch ({wL},{iL}) vs ({wR},{iR})"
    let mut ren : Std.HashMap String String := {}
    for ((nL, _, _, _), (nR, _, _, _)) in sigL.zip sigR do
      ren := ren.insert nR nL
    for pL in m.inputs do
      if !isClockName pL.name then
        -- rt input for original `X` is `_gen_<paramName X>` (or the name
        -- itself if the elaborator kept it)
        let cand := s!"_gen_{paramName pL.name}"
        if m'.inputs.any (·.name == cand) then
          ren := ren.insert cand pL.name
        else if m'.inputs.any (·.name == paramName pL.name) then
          ren := ren.insert (paramName pL.name) pL.name
    -- 5. cones on both sides; rename the reparsed side onto original names
    let (regL, outL) ← match conesOf m with
      | .ok c => pure c | .error e => throwErrorAt f "#verify_dsl_roundtrip (source): {e}"
    let (regR, outR) ← match conesOf m' with
      | .ok c => pure c | .error e => throwErrorAt f "#verify_dsl_roundtrip (reparsed): {e}"
    let regR := regR.map (fun (n, e) => (ren.getD n n, renameRefs ren e))
    let outR := outR.map (fun (n, e) => (n, renameRefs ren e))
    let _ := regOrder
    -- 6. shared binders (original names) + rst = 0 hypotheses
    let wt := widthTable m
    let binderNames : List (String × Nat) :=
      ((m.inputs.filter (fun p => !isClockName p.name)).map (fun p => (p.name, p.ty.bitWidth)))
      ++ sigL.map (fun (n, w, _, _) => (n, w))
    let binders ← binderNames.toArray.mapM fun (n, w) => do
      `(bracketedBinder| ($(varIdent n) : BitVec $(quote w)))
    let rstNames := (sigL.map (fun (_, _, _, r) => r)).eraseDups
    let mut hypBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
    let mut hIdx : Nat := 0
    for r in rstNames do
      let hName := mkIdent (Name.mkSimple s!"hrst_{hIdx}")
      hypBinders := hypBinders.push
        (← `(bracketedBinder| ($hName : $(varIdent r) = (0 : BitVec 1))))
      hIdx := hIdx + 1
    -- 7. obligations: register cones by POSITION, output cone by port
    let mut proven : Nat := 0
    let mut obligations : List (String × Sparkle.IR.AST.Expr × Sparkle.IR.AST.Expr) := []
    for ((nL, _, _, _), (nR, _)) in sigL.zip regR do
      let some eL := (regL.find? (·.1 == nL)).map (·.2)
        | throwErrorAt f "#verify_dsl_roundtrip: cone for {nL} missing"
      let some eR := (regR.find? (·.1 == nR)).map (·.2)
        | throwErrorAt f "#verify_dsl_roundtrip: cone for {nR} missing"
      obligations := obligations ++ [(s!"reg_{nL}", eL, eR)]
    let [outP] := m.outputs | throwErrorAt f "#verify_dsl_roundtrip: one output expected"
    let some oL := (outL.find? (·.1 == outP.name)).map (·.2)
      | throwErrorAt f "#verify_dsl_roundtrip: output cone missing (source)"
    let some oR := ((outR.find? (·.1 == outP.name)) <|> outR.head?).map (·.2)
      | throwErrorAt f "#verify_dsl_roundtrip: output cone missing (reparsed)"
    obligations := obligations ++ [(s!"out_{outP.name}", oL, oR)]
    for (label, eL, eR) in obligations do
      let lhs ← denote wt eL
      let rhs ← denote wt eR
      let thmName := Name.mkSimple
        s!"{declName.toString.replace "." "_"}_dslrt_{Sparkle.Backend.Verilog.sanitizeName label}"
      let thmIdent := mkIdent thmName
      let cmd ←
        `(command| theorem $thmIdent $binders* $hypBinders* : $lhs = $rhs := by
              bv_decide)
      elabCommand cmd
      proven := proven + 1
    logInfoAt stx m!"✅ #verify_dsl_roundtrip `{declName}`: decompiled circuit-DSL re-synthesizes to an equivalent design — {proven} cone obligations proven"
  | _ => throwUnsupportedSyntax

end Tools.SVParser.DslEmit
