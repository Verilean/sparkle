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

/-- Signal-level variable text for an input/register reference. -/
private def refText (regNames : List (String × String)) (n : String) : String :=
  match regNames.find? (·.1 == n) with
  | some (_, dslName) => dslName
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

/-- Render an inlined IR expression (refs are inputs/registers only) as
    circuit-DSL source text. -/
partial def dslExpr (wt : Std.HashMap String Nat)
    (regNames : List (String × String)) :
    Sparkle.IR.AST.Expr → Except String String
  | .const v w =>
    if v < 0 then
      let m : Int := (2 : Int) ^ w
      .ok s!"(Signal.pure ({((v % m + m) % m)}#{w}) : Signal defaultDomain (BitVec {w}))"
    else
      .ok s!"(Signal.pure ({v}#{w}) : Signal defaultDomain (BitVec {w}))"
  | .ref n => .ok (refText regNames n)
  | .slice e hi lo => do
    .ok s!"({← dslExpr wt regNames e})[{hi}, {lo}]"
  | .concat args => do
    match args with
    | [] => .error "empty concat"
    | a :: rest =>
      let mut acc ← dslExpr wt regNames a
      for r in rest do
        acc := s!"({acc} ++ {← dslExpr wt regNames r})"
      .ok acc
  | .op o args => do
    let bin := fun (sym : String) (a b : Sparkle.IR.AST.Expr) => do
      .ok s!"({← dslExpr wt regNames a} {sym} {← dslExpr wt regNames b})"
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
    | .eq, [a, b] => do
      -- The elaborator maps `BEq.beq` to `.eq`; a Bool-valued Signal is
      -- what `Signal.mux` wants as its condition, and lifting it back to
      -- BitVec 1 (for arithmetic contexts) uses the same mux.
      .ok s!"(Signal.mux (Signal.ap (Signal.map (· == ·) {← dslExpr wt regNames a}) {← dslExpr wt regNames b}) (Signal.pure 1#1) (Signal.pure 0#1))"
    | .mux, [c, t, e] => do
      let wc ← widthOf wt c
      if wc != 1 then .error s!"mux condition of width {wc} (v1 supports 1-bit)"
      else
        -- Bool-valued condition without a BitVec detour when the cone is
        -- itself a comparison (the common `.map (· == 1#1)` shape).
        let condTxt ← match c with
          | .op .eq [ca, cb] =>
            .ok s!"(Signal.ap (Signal.map (· == ·) {← dslExpr wt regNames ca}) {← dslExpr wt regNames cb})"
          | _ => .ok s!"(({← dslExpr wt regNames c}).map (· == 1#1))"
        .ok s!"(Signal.mux {condTxt} {← dslExpr wt regNames t} {← dslExpr wt regNames e})"
    | _, _ => .error s!"operator {repr o}/{args.length} not in the v1 circuit-DSL subset"
  | e => .error s!"expression {repr e} not in the v1 circuit-DSL subset"

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
  let dataIns := m.inputs.filter fun p =>
    !isClockName p.name && p.name != "rst" && p.name != "reset"
  let params := String.intercalate " " (dataIns.map fun p =>
    s!"({paramName p.name} : Signal defaultDomain (BitVec {p.ty.bitWidth}))")
  let mut lines : List String := []
  lines := lines ++
    [s!"def {defName} {params} : Signal defaultDomain (BitVec {out.ty.bitWidth}) :="
    , "  circuit do"]
  for ((n, w, init, _), i) in sigs.zipIdx do
    let _ := n
    lines := lines ++ [s!"    let r{i} ← Signal.reg ({init}#{w})"]
  for (n, cone) in regCones do
    let some (_, dslName) := regNames.find? (·.1 == n)
      | .error s!"register {n} missing from name table"
    lines := lines ++ [s!"    {dslName} <~ {← dslExpr wt regNames (simplifyCone wt cone)}"]
  lines := lines ++ [s!"    return {← dslExpr wt regNames (simplifyCone wt outCone)}"]
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
