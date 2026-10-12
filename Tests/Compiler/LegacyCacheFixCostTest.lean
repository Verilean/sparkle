import Tests.Compiler.ShippingInlineSoundnessTest
import Tests.Compiler.ShippingCloseInstsCheckTest
import Tests.Compiler.ShippingMachineTeleTest
import Tests.Compiler.InlineUnfoldRegressionTest

/-! # The cache fix on the success path: same output, and what a snapshot costs

Variant A of the cache fix makes `Rec.tryInlineUnfold` read nine `IO.Ref`
maps before every inline attempt (`snapshotWireCaches`) — on EVERY attempt,
failing or not. Two questions about compiles in which nothing fails:

**(a) Is the emitted design the same?** For each declaration below the
shipping entry (`synthesizeCombinational`) is run and a digest of the result
is logged: the hash of the pretty-printed top module, its statement / wire
counts, the number of modules of the design and the hash of all of them. The
same file is to be run on the main branch and on the fix branch and the two
log lines compared (`DIGEST` lines are byte-comparable).

**(b) How many snapshots, of what size?** The same declarations are compiled
again through the real step with a PROBE around every recursive translation
call (no compiler edit). The probe keeps the stack of the expressions being
translated; a call whose expression is `unfoldDefinition?` of the expression
on top of the stack is the inline attempt's translation call, and the
snapshot — on the fix branch — was taken immediately before it. At that
moment the probe reads the sizes of the nine maps. Logged per declaration:
the number of attempts, and the sum and the maximum of the sizes of (i) the
context's expression cache and (ii) the eight global maps together. A
snapshot shares each map; the first insertion into a shared map copies it,
so `sum` bounds the entries copied because of snapshots in that compile, and
`attempts × max` bounds it from above. The counts are the same on both
branches (the probe does not depend on the fix); only the copying happens on
the fix branch.

Measured with the default front end (the shipping configuration: most of
these declarations then take a certified or the machine route and make few
or no attempts) and with the legacy front end (every helper call is an
attempt).

Declarations: the helper-structured ones of `ShippingInlineSoundnessTest`
(`uRoot` … `uDeep`, and its two IP modules, the DroneCAN node filter and the
MIL-STD-1553 parity), the legacy-fallback parents of
`ShippingCloseInstsCheckTest`, the IP library's HTTP byte machine
(`hftByte`), `plainSig`. A name that is not in the environment is reported,
not an error. Nothing here throws. Limits: these are small designs; the
quadratic risk is in large FSMs with many helper calls, which this file does
not contain (the corpus is not run). -/

open Lean Meta Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.LegacyCacheFixCostTest

/-- What the probe accumulates in one compile. -/
structure Probe where
  attempts : Nat := 0
  exprSum : Nat := 0
  exprMax : Nat := 0
  globalSum : Nat := 0
  globalMax : Nat := 0

/-- `rec` under the probe (see the header). -/
def probeWrap (stack : IO.Ref (List Lean.Expr)) (probe : IO.Ref Probe) (rec : TranslateFn) :
    TranslateFn := fun e hint top named => do
  let parents ← CompilerM.liftMetaM (stack.get : IO (List Lean.Expr))
  match parents with
  | p :: _ =>
    let isAttempt ← CompilerM.liftMetaM (do
      try
        match ← Lean.Meta.unfoldDefinition? p with
        | some e' => pure (e' == e)
        | none => pure false
      catch _ => pure false)
    if isAttempt then
      let ctx ← CompilerM.getCompilerState
      let exprSize ←
        match ctx.exprCache with
        | some ref => CompilerM.liftMetaM (do
            let m ← (ref.get : IO (Lean.ExprStructMap String))
            pure m.size)
        | none => pure 0
      let globalSize ← CompilerM.liftMetaM (do
        let a ← (sparkleLetWireCache.get : IO _)
        let b ← (sparkleLoopWireCache.get : IO _)
        let c ← (sparkleWireCanon.get : IO _)
        let d ← (sparkleSingleOutInstanceCache.get : IO _)
        let f ← (sparkleSubInstanceOutputs.get : IO _)
        let g ← (sparkleWireWidthCache.get : IO _)
        let h ← (sparkleFvarValueMap.get : IO _)
        let i ← (sparkleFvarZetaVisited.get : IO _)
        pure (a.size + b.size + c.size + d.size + f.size + g.size + h.size + i.size))
      CompilerM.liftMetaM (probe.modify (fun pr =>
        { attempts := pr.attempts + 1
        , exprSum := pr.exprSum + exprSize
        , exprMax := max pr.exprMax exprSize
        , globalSum := pr.globalSum + globalSize
        , globalMax := max pr.globalMax globalSize }) : IO Unit)
  | [] => pure ()
  CompilerM.liftMetaM (stack.modify (fun l => e :: l) : IO Unit)
  try
    let w ← rec e hint top named
    CompilerM.liftMetaM (stack.modify (fun l => l.tail) : IO Unit)
    pure w
  catch ex =>
    CompilerM.liftMetaM (stack.modify (fun l => l.tail) : IO Unit)
    throw ex

/-- The digest of a compile's result. -/
def digest (r : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) : String :=
  let m := r.1
  let all : UInt64 := hash ((r.2.modules.map fun x => (repr x).pretty))
  s!"top#{hash (repr m).pretty} stmts={m.body.length} wires={m.wires.length} modules={r.2.modules.length} all#{all}"

/-- The shipping entry's digest, or the error. -/
def realDigest (decl : Name) : MetaM String := do
  try
    let r ← synthesizeCombinational decl
    pure (digest r)
  catch ex =>
    let msg ← ex.toMessageData.toString
    pure s!"REJECTED ({msg})"

/-- One probed compile: its digest and the probe's counts. -/
def probed (cfe : Bool) (decl : Name) : MetaM String := do
  let stack ← IO.mkRef ([] : List Lean.Expr)
  let probe ← IO.mkRef ({} : Probe)
  let tr : TranslateFn :=
    translateFuelFix
      (fun rec => translateStepWith translateFallback (probeWrap stack probe rec)) 4096
  let out : String ←
    try
      let r ← synthesizeCombinationalCoreWith tr decl [] false (certifiedFrontEnd := cfe)
      pure (digest r)
    catch ex =>
      let msg ← ex.toMessageData.toString
      pure s!"REJECTED ({msg})"
  let p ← probe.get
  pure s!"attempts={p.attempts} exprCache(sum={p.exprSum}, max={p.exprMax}) globals(sum={p.globalSum}, max={p.globalMax}) | {out}"

run_cmd Lean.Elab.Command.liftTermElabM do
  try
    let inl : Name := `Sparkle.Tests.Compiler.ShippingInlineSoundnessTest
    let decls : List Name :=
      [inl ++ `uRoot, inl ++ `uCone, inl ++ `uTwice, inl ++ `uNest, inl ++ `uMux, inl ++ `uReg,
       inl ++ `uShare, inl ++ `uLoop, inl ++ `uShadow, inl ++ `uDeep,
       inl ++ `nodeFilterTop, inl ++ `oddParityTop,
       `Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest.useCtr1,
       `Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest.useCtr1Twice,
       `Sparkle.Tests.Compiler.ShippingCloseInstsCheckTest.useMid1,
       `Sparkle.Tests.Compiler.ShippingMachineTeleTest.hftByte,
       `Sparkle.Tests.Compiler.InlineUnfoldRegressionTest.plainSig]
    let env ← getEnv
    let mut lines : String := ""
    let mut total : Nat := 0
    for decl in decls do
      if env.contains decl then
        let d ← realDigest decl
        let pTrue ← probed true decl
        let pFalse ← probed false decl
        lines := lines ++ s!"\n  DIGEST {decl}: {d}\n    PROBE default front end: {pTrue}\n    PROBE legacy front end:  {pFalse}"
        total := total + 1
      else
        lines := lines ++ s!"\n  MISSING {decl}: not in the environment"
    logInfo m!"LEGACY CACHE FIX, COST AND SUCCESS PATH ({total} declarations; compare the DIGEST lines of the main branch and of the fix branch; attempts = inline attempts = snapshots on the fix branch, sizes = the maps' sizes at the snapshot):{lines}"
  catch ex =>
    logInfo m!"LEGACY CACHE FIX, COST AND SUCCESS PATH: harness error: {ex.toMessageData}"

end Sparkle.Tests.Compiler.LegacyCacheFixCostTest
