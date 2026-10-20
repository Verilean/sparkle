# Inventory: `Rec.translateExprToWireImpl` (Sparkle/Compiler/Elab.lean:6930–7983)

Unit B, round 2. Status words: PROVED / PREMISE / OPEN. This file is written BEFORE any proof
(B0); it is updated with the result at the end (see the last section).

Shape of the term. `translateExprToWireImpl rec e hint isTopLevel isNamed : CompilerM String`
(`rec` = the recursive translator, written `translateExprToWire` inside the block). The body is a
`do` block with early `return`s: after elaboration every `if c then (…; return x)` is
`ite c (…) (jp ())` with a join point `jp` for the rest. So an "arm" below is the *then*-branch;
the rest of the block is its else-branch. Arms are walked in this order.

Primitive classes (what the `Keeps`/`KeepsCP` calculus must cover):
* **FR**  = `FramedA` operation (global side ref read/modify, `whnf`, `inferType`, `reduce`,
  `getEnv`, `getConstInfo`, `IO.getEnv`, `mkAppM`, …) → `keepsA_framed` (ShippingChildVCA.lean:71).
* **DG**  = `Diag` (pretty printer) → `keepsA_diag`; **TH** = `throwError` of a message in the
  class → `tripleA_throwErr`.
* **CS**  = circuit-state primitive (`makeWire`, `emitAssign`, `addInput`, `lookupVar`,
  `getWireWidth`, `get`/`set`) → `makeWireP`/`emitAssignP`/`addInputP`/`lookupVarP`… (TranslateA).
* **TC**  = `try … catch` in `CompilerM` (needs `KeepsCP.tryCatch`, not yet in the calculus).
* **TL**  = telescope family: `CompilerM.withLocalDecl` (= `withLocalDeclD`, Elab.lean:136) and
  `CompilerM.withLetDecl` → `RefLawsATele.localDecl/letDecl` (unit C: `keepsCP_withLocalDeclD`,
  `keepsCP_withLetDecl`). NEEDS-TELESCOPE.
* **WV**  = `withVarMapping` (`withVarMappingP`, built).
* **HP**  = helper `def` outside the block, walked separately (`extractNat`, `extractBitVecLiteral`,
  `extractDimExpr`, `cachedInferType`, `inferHWTypeFromSignal`, `lowerZeroExtendWire`,
  `hwTypeFromDim`, `getOperator`, `canonHardwareKey`, …). Their Keeps status is listed per arm.

## A. Prologue (6931–6979)
| arm | lines | calls | prims | status |
|---|---|---|---|---|
| trace + call counter | 6931–6932 | `sparkleCallCounter.modifyGet` | FR (`sideModifyGetIO`) | PROVABLE-NOW |
| runaway limit | 6937–6947 | `IO.getEnv "SPARKLE_TRANSLATE_LIMIT"`, `throwError` | FR (`ioEnv`), TH | PROVABLE-NOW |
| profile dump (every 10000th call) | 6948–6977 | `IO.getEnv`, 9 side-ref reads, `IO.eprintln`, `Sparkle.Compiler.flushStderr`, `IO.FS.Handle.mk "/tmp/sparkle-profile.log"`, `putStrLn`, `flush`, string building | FR for the ref reads; **file/stderr IO is NOT in `FramedA`** | NEEDS-IO (a `profileDump` premise, see below) |

## B. `.fvar` first (6981–7033) — arm `fvarArm`
`CompilerM.lookupVar`; `lctx.find?`/`decl.value?` in `MetaM` (`getLCtx`); cycle break via
`sparkleFvarZetaVisited` (side ref read/modify) with `throwError`; recursive `translateExprToWire`
on the fvar's value inside `try/finally`-like restore of the visited set. prims: CS, FR, TH,
`rec`. status: PROVABLE-NOW if `tryFinally`/`modify` are in the calculus (`Triple.tryFinally`
exists, ShippingChildKeeps); otherwise the arm is premise `FVarZetaArmA`.

## C. Early interception of Signal operators (7043–7085) — `signalBinOpArm`, `signalAppendArm`
`signalBinOpOf`, `canonicalSignalBinKinds` (pure), `translateCanonicalSignalBinary` (already
PROVED as `translateCanonicalSignalBinaryA`, TranslateA), `cachedInferType` (HP: reads
`sparkleTypeCache`, FR), `inferHWTypeFromSignal` (HP: `whnf`/`getEnv`, FR/TH), `makeWire`,
`emitAssign`, `extractBitVecLiteral` (HP, TH), 2× `rec`. PROVABLE-NOW given Keeps lemmas for the
three HP helpers (`ShippingChildHelpers.lean` has them under the OLD boundary only).

## D. High-priority `.const` arms (7087–7670), in order
| # | arm | lines | prims | status |
|---|---|---|---|---|
| D1 | `OfNat.ofNat` literal | 7090–7098 | `whnf`, `extractNat`, CS | PROVABLE-NOW |
| D2 | `Bool.true` / `Bool.false` | 7100–7108 | CS | PROVABLE-NOW |
| D3 | `OfNat.mk` unwrap | 7110–7111 | `rec` | PROVABLE-NOW |
| D4 | Signal wrappers / identity casts | 7115–7123 | `rec` | PROVABLE-NOW |
| D5 | `Signal.pure` / `Signal.lit` | 7125–7168 | `translateSignalPureLiteral?` (pure), `whnf`, `lookupVar`, TC (`try extractBitVecLiteral catch … reduce …`), CS, `rec` | needs TC |
| D6 | `bundle2` | 7170–7178 | `rec`×2, `cachedInferType`, CS | PROVABLE-NOW |
| D7 | `Signal.map` with `Prod.fst`/`Prod.snd` | 7180–7220 | `rec`, `getWireWidth` (side-ref read), CS | PROVABLE-NOW |
| D8 | `Signal.map` lambda: extractLsb', zeroExtend/setWidth, signExtend, sshiftRight, unary | 7222–7300 | `extractDimExpr`, `lowerZeroExtendWire`, `getWireWidth`, CS, `rec` | PROVABLE-NOW |
| D9 | `Signal.map` composite-body lambda + local `toIR` (`let rec`) | 7302–7362 | **TL** (`withLocalDecl`), WV, **TC** (`try extractBitVecLiteral catch`), recursion on sub-expression (`toIR`) | NEEDS-TELESCOPE |
| D10 | `ite`/`dite` error | 7365–7373 | `ppExpr` (DG), `throwError` | PROVABLE-NOW |
| D11 | `Decidable.rec/casesOn` error | 7375–7381 | TH | PROVABLE-NOW |
| D12 | `Prod.rec/casesOn` | 7385–7486 | `reduce` (FR), `rec`, **TL**×(1–2) + WV, `lctx.find?`, `throwError`, CS | NEEDS-TELESCOPE |
| D13 | `Seq.seq` of Signal → `translateExprToWireApp` | 7488–7490 | the App dispatcher (section G) | PREMISE-of-G |
| D14 | `Seq.seq (Functor.map f a) b` | 7492–7560 | `rec`×2, `getPrimitiveNameFromLambda` (recursive def, induction), `cachedInferType`, CS | PROVABLE-NOW |
| D15 | `Functor.map` | 7562–7669 | `extractDimExpr`, `lowerZeroExtendWire`, `extractBitVecLiteral`, `getOperator`, `rec`, CS | PROVABLE-NOW |

## E. Reduction (7671–7690)
`getCompilerState`, `e.find?` (pure), `whnf` at `reducible` transparency (FR + `withTransparency`
= `withReader` on the Meta context: needs the context-update rule with `admCtx_config`).
PROVABLE-NOW.

## F. The final `match e` (7691–7981)
| arm | lines | prims | status |
|---|---|---|---|
| `.app` with `.const` head → App dispatcher | 7692–7694 | G | PREMISE-of-G |
| `.app` zeta of a let-bound head | 7695–7716 | `getLCtx`, `whnf` at default, `rec`, G | PROVABLE-NOW + G |
| `.proj` | 7719–7805 | `whnf` at `all`, `getEnv`, `inferType`, `whnf`, `throwError`, `rec`×2–3, `cachedInferType`, CS | PROVABLE-NOW |
| `.lit (.natVal n)` | 7807–7814 | CS | PROVABLE-NOW |
| `.fvar` | 7816–7822 | `lookupVar`, `getCompilerState`, `throwError` | PROVABLE-NOW |
| `.letE` | 7824–7929 | TC (`try inferHWTypeFromSignal`), `canonHardwareKey` (HP, premise `CanonKeyA`, unit A), `sparkleLetWireCache` read/modify (FR), `makeWire`/`emitAssign`, **TL** `withLocalDecl`/`withLetDecl`, WV, `sparkleFvarValueMap.modify`, `rec` | NEEDS-TELESCOPE |
| `.lam` | 7931–7972 | TC, `inferHWTypeFromSignal`, `get`, `makeWire`, `addInput`, **TL** `withLocalDecl`, WV, `rec` | NEEDS-TELESCOPE |
| `_` → G | 7974–7978 | G | PREMISE-of-G |

## G. `Rec.translateExprToWireApp` (6804–6919), called from D13, F(.app), F(_)
Its own arms: `handleErrorPatterns` (5707), `PUnit.unit`/`Unit.unit` literal, `Signal.pure` unit
terminator (`inferType`+`whnf`), the local `normSpine` (recursive on fuel: `whnfUntil` FR,
`inlCanonLam`/`inlCanonPi` pure), then the handler chain, in order:
`handleCircuitMonad` (6240) · `handleTupleProjections` (5725) · `handleApplicative` (5840, with
`lower`) · `handleBitVecOps` (5885, with `translateShiftAmount`) · `handleRegister` (5975) ·
`handleMux` (6010) · `handleMemory` (6050) · `handleLoop` (6125) · `handleDefinitionUnfold`
(6401, with `tryInlineUnfold` 6345, `snapshotWireCaches`/`restoreWireCaches` 5670/5689), then
the closing `throwError`s. These are separate `def`s of the file; each is named after itself.
The OLD proofs of every one of them exist (`Tools/ShippingChildLegacy.lean`, by the tactic `vc`
under `RefLaws L`); none is ported to the admissible boundary.

## The premises this inventory fixes (names for `legacyImplA_of_handlers`)
(see the end of the file for what was finally proved vs. left as premise)
