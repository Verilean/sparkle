import Tools.ShippingFGCircuitS3b2Final
import Tests.Gen5.FGCircuitPilotCheck45
set_option autoImplicit false
-- FG circuit pilot Check46r (S3b2, route B): A) controls of the concrete reader check and of the pilot entry on the real environment (True / another environment / another child / another lvl / altered data), the output comparison and the explicit error; B) complete types against independently written statements (ONE criterion FGCircuitCmp.stmtEq for the expected statement and every mutant); C) axioms. docs/FG-CIRCUIT-PILOT.md §53.
open Lean Elab Command Tools.ShippingFGCircuitS3b2Reader Tools.ShippingFGCircuitS3b2Exp Tools.ShippingFGCircuitS3b2Final Tools.ShippingFGCircuitS1kStmt
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## A. controls on the real environment -/
run_cmd liftTermElabM do
  let env ← getEnv
  let ok (b : Bool) (msg : String) : MetaM Unit := unless b do throwError "FGCIRCUIT46R control failed: {msg}"
  -- the real environment passes (the real dataOfAt at lvl₀ returns the children's machineData)
  ok (pilotReaderOk env hftRoot) "real environment: true"
  ok (rootReaderB lvl₀ env hftHttp httpMD) "http child true"
  ok (rootReaderB lvl₀ env hftTlp tlpMD) "tlp child true"
  -- another declaration, another child's data (both directions), a missing constant
  ok (!pilotReaderOk env `Some.Other.Decl) "another root"
  ok (!pilotReaderOk env hftHttp) "the child as root"
  ok (!rootReaderB lvl₀ env hftHttp tlpMD) "http child against the tlp data"
  ok (!rootReaderB lvl₀ env hftTlp httpMD) "tlp child against the http data"
  ok (!rootReaderB lvl₀ env `Sparkle.NoSuchConstant httpMD) "missing constant"
  -- altered data: every component the comparison covers
  let m := httpMD
  ok (!rootReaderB lvl₀ env hftHttp { m with nIn := m.nIn + 1 }) "nIn altered"
  ok (!rootReaderB lvl₀ env hftHttp { m with dom := mkNatLit 0 }) "dom altered"
  ok (!rootReaderB lvl₀ env hftHttp { m with bposL := 0 :: m.bposL }) "bposL altered"
  ok (!rootReaderB lvl₀ env hftHttp { m with vwL := m.vwL.reverse ++ [1] }) "vwL altered"
  ok (!rootReaderB lvl₀ env hftHttp { m with ls := m.ls ++ m.ls }) "ls altered (doubled)"
  ok (!rootReaderB lvl₀ env hftHttp { m with outs := m.outs.reverse ++ m.outs }) "outs altered (order / doubled)"
  ok (!rootReaderB lvl₀ env hftHttp { m with shape := { m.shape with body := mkNatLit 0 } }) "shape.body altered"
  ok (!rootReaderB lvl₀ env hftHttp { m with shape := { m.shape with binders := m.shape.binders.reverse } }) "shape.binders reversed"
  ok (mdBeq m m) "mdBeq reflexive on the real data"
  -- another environment: only `Init` imported
  let env' ← importModules #[{ module := `Init }] {} (loadExts := false)
  ok (!pilotReaderOk env' hftRoot) "Init-only environment: false (the checker is not True)"
  ok (!rootReaderB lvl₀ env' hftHttp httpMD) "Init-only environment, http child: false"
  -- another lvl: at these two children the Bool check is true at small constant levels as well, so the check does not tell lvl apart; the certified lvl is a property of the STATEMENT (section B)
  let lvOk (k : Nat) : Bool := rootReaderB (fun _ => k) env hftHttp httpMD && rootReaderB (fun _ => k) env hftTlp tlpMD
  logInfo m!"FGCIRCUIT46R CONTROLS: ok (real env true; other root / child as root / swapped children / missing constant / 8 altered-data components / Init-only environment false); lvl: the check at constant levels 0, 1, 3, 10 and lvl₀ gives {[lvOk 0, lvOk 1, lvOk 3, lvOk 10, lvOk (lvl₀ (mkNatLit 0))]} (lvl is distinguished by the statements, section B)"

-- the REAL pilot entry against the existing entry and the existing core: the same Module and Design, and the printed text is the one of the Module THIS run returned -/
run_cmd liftTermElabM do
  let X := hftRoot
  let t0 ← IO.monoMsNow
  let (m1, d1, v1) ← pilotArtifact X
  let t1 ← IO.monoMsNow
  let (m2, d2) ← Sparkle.Compiler.Elab.synthesizeCombinationalOff X
  let t2 ← IO.monoMsNow
  let (m3, d3) ← Sparkle.Compiler.Elab.synthesizeCombinationalOffR (fun _ _ => true) X
  let rp (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) : String := toString (repr m) ++ "\n" ++ toString (repr d)
  unless rp m1 d1 == rp m2 d2 do throwError "FGCIRCUIT46R OUTPUT: the pilot entry and the existing Off entry differ"
  unless rp m3 d3 == rp m2 d2 do throwError "FGCIRCUIT46R OUTPUT: the entry with a True check and the existing Off entry differ"
  unless v1 == Sparkle.Compiler.Elab.verilogOf m2 do throwError "FGCIRCUIT46R OUTPUT: the text printed from the pilot run differs from the existing entry's"
  -- the explicit error: a false check refuses (no fallback)
  let msg ← try
      discard <| Sparkle.Compiler.Elab.synthesizeCombinationalOffR (fun _ _ => false) X
      pure "NO ERROR"
    catch e => e.toMessageData.toString
  unless msg.contains "reader check" && msg.contains "refusing to synthesize" do throwError "FGCIRCUIT46R ERROR control: {msg}"
  -- the pilot entry on another declaration refuses (the check names the pilot root)
  let msg2 ← try
      discard <| pilotEntry hftHttp
      pure "NO ERROR"
    catch e => e.toMessageData.toString
  unless msg2.contains "reader check" do throwError "FGCIRCUIT46R ERROR control (another declaration): {msg2}"
  logInfo m!"FGCIRCUIT46R OUTPUT: module+design repr of the pilot entry = the existing Off entry = the entry with a True check ({(toString (repr m1)).length} / {(toString (repr d1)).length} chars); the Verilog text printed from the pilot run's own Module is identical to the existing entry's ({v1.length} chars; no second synthesis for the print); a false check gives the explicit error '{msg}'; the pilot entry on another declaration refuses ({msg2.length} chars of error). Pilot entry {t1-t0} ms, existing Off {t2-t1} ms (ONE run each; not a cost claim)"

/-! ## B. complete types against independently written statements -/
namespace Tests.Gen5.FGCircuitPilotCheck46r
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kStmt (hftRoot hftHttp hftTlp)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod NmRoot NmHttp NmTlp ShE RootData HttpData TlpData Pre)
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)
open Tests.Gen5.FGCircuitPilotCheck43 (CVT FD4)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff)
open Tests.Gen5.FGCircuitPilotCheck44 (envX NmHttpX)
open Tools.ShippingFGCircuitCover (RootReader)
open Tools.ShippingFGCircuitS1iEnv (CheckedStart)
open Tools.ShippingFGCircuitS1qEndpoint (PostRunOff)
open Tools.ShippingFGCircuitArtifact
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingChildInvA (AdmCtx)
open Sparkle.IR.AST (Design)
open Sparkle.Compiler.Elab (synthesizeCombinationalOff synthesizeCombinationalOffR)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingGen2 Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead

def lvlZero : Lean.Expr → Nat := fun _ => 0
def lvlSucc : Lean.Expr → Nat := fun e => Tools.ShippingFGCircuitS3b2Reader.lvl₀ e + 1
def chkTrue : Environment → Name → Bool := fun _ _ => true

/-- (1) the soundness of the check, written again. Knobs: the check, the environment it is run at and the one the conclusion speaks about, the level, the children (names / data), the root equation -/
noncomputable def ExpSnd (chk : Environment → Name → Bool) (ec ee : Environment → Environment) (lv : Lean.Expr → Nat)
    (nH nT : Name) (dH dT : MachineData) (needRoot : Bool) : Prop :=
  ∀ {env : Environment} {X : Name}, chk (ec env) X = true →
    (if needRoot then X = hftRoot else True) ∧ RootReader lv (ee env) nH dH ∧ RootReader lv (ee env) nT dT

noncomputable def Snd (chk : Environment → Name → Bool := Tools.ShippingFGCircuitS3b2Final.pilotReaderOk) (ec ee : Environment → Environment := fun e => e)
    (lv : Lean.Expr → Nat := Tools.ShippingFGCircuitS3b2Reader.lvl₀) (nH : Name := NmHttp) (nT : Name := NmTlp) (dH : MachineData := HttpData) (dT : MachineData := TlpData)
    (needRoot : Bool := true) : Prop := ExpSnd chk ec ee lv nH nT dH dT needRoot

noncomputable def Snd_real : Prop := Snd
noncomputable def SndMu_true : Prop := Snd (chk := chkTrue)
noncomputable def SndMu_envCheck : Prop := Snd (ec := envX)
noncomputable def SndMu_envConcl : Prop := Snd (ee := envX)
noncomputable def SndMu_lvlZero : Prop := Snd (lv := lvlZero)
noncomputable def SndMu_lvlSucc : Prop := Snd (lv := lvlSucc)
noncomputable def SndMu_swapNames : Prop := Snd (nH := NmTlp) (nT := NmHttp)
noncomputable def SndMu_swapData : Prop := Snd (dH := TlpData) (dT := HttpData)
noncomputable def SndMu_httpTwice : Prop := Snd (nT := NmHttp) (dT := HttpData)
noncomputable def SndMu_rootData : Prop := Snd (dH := RootData)
noncomputable def SndMu_noRoot : Prop := Snd (needRoot := false)

/-- (2) the guard from the run, written again: a successful run of the checked entry on `root` passed `readerOk` at `eA` -/
noncomputable def ExpGuard (root chkRoot : Name) (needCell : Bool) (eA : EnvK) : Prop :=
  ∀ {readerOk : Environment → Name → Bool} {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {w w' : W} {b : Mod} {D' : Design},
    Pre needCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    RunsTo (synthesizeCombinationalOffR readerOk root) mctx mref cctx cref w (b, D') w' →
    readerOk (eA cref w w' (envX (envAt cref w))) chkRoot = true)

/-- the knob form: the environment is `eA` applied to a dummy `env₀` replaced by the run's own start environment (`eS`) -/
noncomputable def Guard (root chkRoot : Name := hftRoot) (needCell : Bool := true) (eA : EnvK := eS) : Prop :=
  ∀ {readerOk : Environment → Name → Bool} {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {w w' : W} {b : Mod} {D' : Design},
    Pre needCell (CellPrem Tools.ShippingChildFresh.MkRefd mref cref) (
    RunsTo (synthesizeCombinationalOffR readerOk root) mctx mref cctx cref w (b, D') w' →
    readerOk (eA cref w w' (envAt cref w)) chkRoot = true)

noncomputable def Guard_real : Prop := Guard
noncomputable def GuardMu_end : Prop := Guard (eA := eE)
noncomputable def GuardMu_env0 : Prop := ∀ {e0' : Environment}, Guard (eA := fun _ _ _ _ => e0')
noncomputable def GuardMu_root : Prop := Guard (root := NmHttpX)
noncomputable def GuardMu_chkRoot : Prop := Guard (chkRoot := NmHttpX)
noncomputable def GuardMu_noCell : Prop := Guard (needCell := false)

/-- (3) the bridge, written again: the checked entry's run is a run of the EXISTING entry with the same declaration, contexts, worlds, Module and Design -/
noncomputable def Bridge_real : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D') w'
noncomputable def BridgeMu_endW : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' w'' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D') w''
noncomputable def BridgeMu_startW : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w0 w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w0 (b, D') w'
noncomputable def BridgeMu_mod : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b b' : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b', D') w'
noncomputable def BridgeMu_design : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' D'' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D'') w'
noncomputable def BridgeMu_decl : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName declName' : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName') mctx mref cctx cref w (b, D') w'
noncomputable def BridgeMu_diag : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (b, D') w'
noncomputable def BridgeMu_core : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (b, D') w'
noncomputable def BridgeMu_reverse : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOff declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w'
noncomputable def BridgeMu_ctx : Prop :=
  ∀ {mctx mctx' : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (synthesizeCombinationalOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (synthesizeCombinationalOff declName) mctx' mref cctx cref w (b, D') w'

/-- the core bridge (3a) -/
noncomputable def CoreBridge_real : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b : Mod} {D' : Design},
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (b, D') w'
noncomputable def CoreBridgeMu_endW : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' w'' : W} {b : Mod} {D' : Design},
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (b, D') w''
noncomputable def CoreBridgeMu_mod : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w' : W} {b b' : Mod} {D' : Design},
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (b', D') w'
noncomputable def CoreBridgeMu_startW : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {readerOk : Environment → Name → Bool} {declName : Name} {w w0 w' : W} {b : Mod} {D' : Design},
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOffR readerOk declName) mctx mref cctx cref w (b, D') w' →
    RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName) mctx mref cctx cref w0 (b, D') w'

/-- (4) the final statement v7r, written again.  Knobs: the check of the entry, the level of `hchk` / of the two readers (kept as premises when `needRd`) / of `GPt`, the root, the start / conclusion environments, the output shape -/
noncomputable def Exp7R (chk : Environment → Name → Bool) (lvC lvR lvG : Lean.Expr → Nat) (needRd : Bool)
    (eA cE : EnvK) (root postRoot : Name) (sh : SigShape) (needAdm : Bool) : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w →
    RunsTo (synthesizeCombinationalOffR chk root) mctx mref cctx cref w (b, D') w' →
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    CheckedStart lvC env₀ cref w root hftRootType hftRootValue RootData →
    Pre needRd (RootReader lvR (envAt cref w) NmHttp HttpData) (
    Pre needRd (RootReader lvR (envAt cref w) NmTlp TlpData) (
    Pre needAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) w) mctx cctx) (
    Pre true (ExpDown L.O (eA cref w w' env₀) w) (
    Pre true (ExpD L.O (eA cref w w' env₀) w) (
    Pre true (ExpG L.O (eA cref w w' env₀) w) (
    Pre true (ExpT L.O (eA cref w w' env₀) w) (
    Pre true (ExpPS L.O w) (
    Pre true (ExpProfOff mref cref w) (
    (∃ raw, PostRunOff mctx mref cctx cref w postRoot D' b raw) ∧
    (∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CVT (cE cref w w' env₀) (GPt (ι := ι) lvG (cE cref w w' env₀)) (PostRunOff mctx mref cctx cref w postRoot D') NmRoot sh mm b D' p))))))))))

noncomputable def F7 (chk : Environment → Name → Bool := Tools.ShippingFGCircuitS3b2Final.pilotReaderOk)
    (lvC lvR lvG : Lean.Expr → Nat := Tools.ShippingFGCircuitS3b2Reader.lvl₀) (needRd : Bool := false)
    (eA cE : EnvK := eS) (root postRoot : Name := NmRoot) (sh : SigShape := ShE) (needAdm : Bool := true) : Prop :=
  Exp7R chk lvC lvR lvG needRd eA cE root postRoot sh needAdm

noncomputable def F7_real : Prop := F7
noncomputable def F7Mu_true : Prop := F7 (chk := chkTrue)
noncomputable def F7Mu_chkOther : Prop := F7 (chk := fun env X => Tools.ShippingFGCircuitS3b2Final.pilotReaderOk env X && false)
noncomputable def F7Mu_lvlChk0 : Prop := F7 (lvC := lvlZero)
noncomputable def F7Mu_lvlChkSucc : Prop := F7 (lvC := lvlSucc)
noncomputable def F7Mu_lvlGPt0 : Prop := F7 (lvG := lvlZero)
noncomputable def F7Mu_lvlGPtSucc : Prop := F7 (lvG := lvlSucc)
noncomputable def F7Mu_readersKept : Prop := F7 (needRd := true)
noncomputable def F7Mu_readersKeptLvl0 : Prop := F7 (needRd := true) (lvR := lvlZero)
noncomputable def F7Mu_root : Prop := F7 (root := NmHttpX)
noncomputable def F7Mu_postRoot : Prop := F7 (postRoot := NmHttp)
noncomputable def F7Mu_reachEnd : Prop := F7 (eA := eE)
noncomputable def F7Mu_reachEnv0 : Prop := F7 (eA := e0)
noncomputable def F7Mu_concEnd : Prop := F7 (cE := eE)
noncomputable def F7Mu_concEnv0 : Prop := F7 (cE := e0)
noncomputable def F7Mu_output : Prop := F7 (sh := { ShE with res := .one (.bits 16) })
noncomputable def F7Mu_noAdm : Prop := F7 (needAdm := false)
/-- the old entry in the hypothesis (no check): the conclusion would be the v6-without-readers statement, which is NOT proved -/
noncomputable def F7Mu_oldEntry : Prop :=
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2} (L : Laws mref cref) (env₀ : Environment) {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w → RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w' → CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    CheckedStart Tools.ShippingFGCircuitS3b2Reader.lvl₀ env₀ cref w hftRoot hftRootType hftRootValue RootData → True

def unfold46 : List Name := [``Tools.ShippingFGCircuitS3b2Final.HftFinalStmtOffCombined7R, ``Tools.ShippingFGCircuitS3aFinal.HftFinalStmtOffCombined6, ``Tools.ShippingFGCircuitS2zFinal.HftFinalStmtOffCombined5, ``Tools.ShippingFGCircuitS2yFinal.cdvT]
def norm46 (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold46.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
  norm37 e

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck46r ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- 1. soundness of the check
  let snd ← norm46 (← tyOf ``Tools.ShippingFGCircuitS3b2Final.pilotReaderOk_sound)
  Tests.Gen5.FGCircuitCmp.checkSame "pilotReaderOk_sound" snd (← norm37 (Q "Snd_real"))
  for mu in ["SndMu_true", "SndMu_envCheck", "SndMu_envConcl", "SndMu_lvlZero", "SndMu_lvlSucc", "SndMu_swapNames", "SndMu_swapData", "SndMu_httpTwice", "SndMu_rootData", "SndMu_noRoot"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"pilotReaderOk_sound vs {mu}" snd (← norm37 (Q mu)); nm := nm + 1
  -- 2. the guard from the run (any readerOk)
  let gd ← norm46 (← tyOf ``Tools.ShippingFGCircuitS3b2Final.readerOk_of_run)
  Tests.Gen5.FGCircuitCmp.checkSame "readerOk_of_run" gd (← norm37 (Q "Guard_real"))
  for mu in ["GuardMu_end", "GuardMu_env0", "GuardMu_root", "GuardMu_chkRoot", "GuardMu_noCell"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"readerOk_of_run vs {mu}" gd (← norm37 (Q mu)); nm := nm + 1
  -- 3. the bridges
  let br ← norm46 (← tyOf ``Tools.ShippingFGCircuitS3b2Core.offR_to_off)
  Tests.Gen5.FGCircuitCmp.checkSame "offR_to_off" br (← norm37 (Q "Bridge_real"))
  for mu in ["BridgeMu_endW", "BridgeMu_startW", "BridgeMu_mod", "BridgeMu_design", "BridgeMu_decl", "BridgeMu_diag", "BridgeMu_core", "BridgeMu_reverse", "BridgeMu_ctx"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"offR_to_off vs {mu}" br (← norm37 (Q mu)); nm := nm + 1
  let cb ← norm46 (← tyOf ``Tools.ShippingFGCircuitS3b2Core.coreR_to_core)
  Tests.Gen5.FGCircuitCmp.checkSame "coreR_to_core" cb (← norm37 (Q "CoreBridge_real"))
  for mu in ["CoreBridgeMu_endW", "CoreBridgeMu_mod", "CoreBridgeMu_startW"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"coreR_to_core vs {mu}" cb (← norm37 (Q mu)); nm := nm + 1
  -- 4. v7r
  let f7 ← norm46 (← tyOf ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined7R" f7 (← norm37 (Q "F7_real"))
  for mu in ["F7Mu_true", "F7Mu_chkOther", "F7Mu_lvlChk0", "F7Mu_lvlChkSucc", "F7Mu_lvlGPt0", "F7Mu_lvlGPtSucc", "F7Mu_readersKept", "F7Mu_readersKeptLvl0", "F7Mu_root", "F7Mu_postRoot",
      "F7Mu_reachEnd", "F7Mu_reachEnv0", "F7Mu_concEnd", "F7Mu_concEnv0", "F7Mu_output", "F7Mu_noAdm", "F7Mu_oldEntry"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined7R vs {mu}" f7 (← norm37 (Q mu)); nm := nm + 1
  -- v7r is not v6 (v6 keeps `lvl`, `hreadH`, `hreadT` and speaks about the existing entry), and v6 is untouched
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined7R vs the v6 theorem's type" f7 (← norm46 (← tyOf ``Tools.ShippingFGCircuitS3aFinal.synth_hftPcieOutByte_finalOffCombined6)); nm := nm + 1
  logInfo m!"FGCIRCUIT46R SIGNATURES: the complete types of pilotReaderOk_sound, readerOk_of_run, offR_to_off, coreR_to_core and synth_hftPcieOutByte_finalOffCombined7R equal the independently written statements under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected (check True / the check never true; check run at or concluded for another environment; lvl 0 / lvl₀+1 for the readers, for hchk, for GPt; readers kept as premises (also at lvl 0); other root / post root / output shape; start / end / env₀ environments of the reach and conclusion; the old entry in the hypothesis; swapped children names / data, child twice, root data for a child, root equation dropped; for the bridges: another end / start world, Module, Design, declaration, context, the diagnostic entry, the core, the reverse direction; cell premise dropped; and the v6 statement)"

run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``Tools.ShippingFGCircuitS3b2Reader.mdBeq_eq, ``Tools.ShippingFGCircuitS3b2Reader.rootReaderB_sound, ``Tools.ShippingFGCircuitS3b2Exp.httpMD_eq,
    ``Tools.ShippingFGCircuitS3b2Exp.tlpMD_eq, ``Tools.ShippingFGCircuitS3b2Core.coreR_chain, ``Tools.ShippingFGCircuitS3b2Core.coreR_to_core, ``Tools.ShippingFGCircuitS3b2Core.offR_to_off,
    ``Tools.ShippingFGCircuitS3b2Final.pilotReaderOk_sound, ``Tools.ShippingFGCircuitS3b2Final.readerOk_of_run, ``Tools.ShippingFGCircuitS3b2Final.synth_hftPcieOutByte_finalOffCombined7R]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT46R AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck46r
