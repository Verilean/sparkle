import Tools.ShippingGen5CVFinal
import Tools.ShippingGen5ConstValueEV
set_option autoImplicit false
-- D.D-4 final scan (Issue sparkle-ledger-dd4-final). No sorry / axiom / native_decide.

/-! # The final root and its consumers do not require the old carriers

The OLD carriers are the inductive families `CVE*` / `TDen*` / `ArgsDen*` declared in `ConstValueE` (`CVE`), `ConstValueES` (`CVEKS`), `ConstValueESL` (`CVEKL`), `ConstValueEKey` (`CVEK`), and the
opaque-level valuation carrier `ConstValueEV` (`CVEKV` there; the final one is `ConstValueEVL.CVEKV`). The theory stays in the repository for history and comparison; the final root must not reach it.

The scan walks the closure of a root: for every reached constant the constants of its type and (for definitions, theorems, opaque) of its value, plus the constructors of an inductive type. Constants of
modules outside the project (`Init` / `Std` / `Lean` / ...) are recorded but not expanded (they cannot refer to project code). A violation is a reached constant that is one of the OLD inductives (a constructor, recursor
or any theorem about them reaches the inductive through its type). Roots: the final ones (`CVFinal`, its theorems, `FGLedgerPremisesStmtCV` and the two bridges) and the downstream consumers that take a `CV`
(`DeclConnect`, `ConstValueFunctional`, `FGLedgerPremisesStmtH` / `G`, `genGP`). Negative controls: the old roots (`cvlsks_functional`, `cvls_functional`, `cvlskl_functional`, EV's `cvlskv_functional`, `CVLSK`) are detected. -/
open Lean Meta

namespace Tests.Gen5.CVFinalScan

def projectModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some i =>
    let m := env.header.moduleNames[i.toNat]!
    let r := m.getRoot
    r == `Tools || r == `Tests || r == `Sparkle

def oldModules : List Name :=
  [`Tools.ShippingGen5ConstValueE, `Tools.ShippingGen5ConstValueES, `Tools.ShippingGen5ConstValueESL, `Tools.ShippingGen5ConstValueEKey, `Tools.ShippingGen5ConstValueEV]

def carrierLike (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "CVE" || s.startsWith "TDen" || s.startsWith "ArgsDen"
  | _ => false

/-- The old carrier inductives: `CVE*` / `TDen*` / `ArgsDen*` inductive types declared in the old modules. -/
def oldInductives (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in oldModules do
    let some idx := env.getModuleIdx? m | continue
    for (n, ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx && carrierLike n then
        if let .inductInfo _ := ci then s := s.insert n
  return s

def usedOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  let v := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | .thmInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray
    | _ => #[]
  t ++ v

structure Scan where
  reached : Nat
  expanded : Nat
  violations : Array (Name × List Name)  -- old inductive, path from the root
  seen : NameMap Name

/-- Breadth-first closure with parent pointers. -/
def scan (env : Environment) (old : NameSet) (roots : Array Name) : Scan := Id.run do
  let mut seen : NameMap Name := {}
  let mut queue : Array Name := #[]
  for r in roots do
    seen := seen.insert r .anonymous
    queue := queue.push r
  let mut i := 0
  let mut expanded := 0
  let mut viol : Array (Name × List Name) := #[]
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if old.contains n then
      let mut path : List Name := [n]
      let mut cur := n
      for _ in [0:40] do
        match seen.find? cur with
        | some p => if p.isAnonymous then break else path := p :: path; cur := p
        | none => break
      viol := viol.push (n, path)
    if projectModule env n then
      if let some ci := env.find? n then
        expanded := expanded + 1
        for u in usedOf ci do
          unless seen.contains u do
            seen := seen.insert u n
            queue := queue.push u
  return { reached := seen.size, expanded, violations := viol, seen }

def finalRoots : Array Name := #[
  ``Tools.ShippingGen5CVFinal.CVFinal, ``Tools.ShippingGen5CVFinal.cvFinal_functional, ``Tools.ShippingGen5CVFinal.cvFinal_iff,
  ``Tools.ShippingGen5CVFinal.cvFinal_value_unique, ``Tools.ShippingGen5CVFinal.cvFinal_typed, ``Tools.ShippingGen5CVFinal.cvFinal_ne_top,
  ``Tools.ShippingGen5CVFinal.declConnect_cvFinal_iff, ``Tools.ShippingGen5CVFinal.declConnect_cvFinal_unique,
  ``Tools.ShippingGen5CVFinal.declConnect_cvFinal_typed, ``Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV,
  ``Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_H, ``Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_G,
  ``Tools.ShippingGen5CVFinal.envDeclClosed_of_premises]

/-- Downstream consumers of a `CV` (they take it abstractly) and the statements the final one is derived from. -/
def consumerRoots : Array Name := #[
  ``Tools.ShippingGen5DeclConnect.DeclConnect, ``Tools.ShippingGen5DeclConnect.DeclConnectAt, ``Tools.ShippingGen5FG.ConstValueFunctional,
  ``Tools.ShippingGen5DeclConnect.declConnect_of_rows, ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH,
  ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG, ``Tools.ShippingGenFGLedgerPremises.genGP]

def oldRoots : Array Name := #[
  ``Tools.ShippingGen5ConstValueES.cvlsks_functional, ``Tools.ShippingGen5ConstValueE.cvls_functional,
  ``Tools.ShippingGen5ConstValueESL.cvlskl_functional, ``Tools.ShippingGen5ConstValueEV.cvlskv_functional,
  ``Tools.ShippingGen5ConstValueEKey.CVLSK]

def show' (s : Scan) : String :=
  s!"reached {s.reached}, expanded {s.expanded}, old-carrier hits {s.violations.size}"

run_meta do
  let env ← getEnv
  let old := oldInductives env
  let names := old.toList.map (·.toString)
  if names.length < 8 then throwError "too few old carrier inductives found: {names}"
  for n in finalRoots ++ consumerRoots ++ oldRoots do
    unless env.contains n do throwError "root {n} does not exist"
  -- the new carrier is not among the old ones
  unless !old.contains ``Tools.ShippingGen5ConstValueEVL.CVEKV do throwError "EVL.CVEKV classified as old"
  let sf := scan env old finalRoots
  let sc := scan env old consumerRoots
  let mut so : Array (Name × Scan) := #[]
  for r in oldRoots do so := so.push (r, scan env old #[r])
  -- control: the scanner reaches a known project dependency of the final root (EVL's CVEKV)
  let sEVL := scan env old #[``Tools.ShippingGen5CVFinal.cvFinal_functional]
  unless (sEVL.seen.contains ``Tools.ShippingGen5ConstValueEVL.CVEKV) && (sEVL.seen.contains ``Tools.ShippingGen5ConstValueE.LS) do
    throwError "CONTROL: scan of cvFinal_functional does not reach EVL.CVEKV / LS ({sEVL.reached} constants)"
  -- NEGATIVE CONTROLS: every old root is detected
  for (r, s) in so do
    if s.violations.isEmpty then throwError "CONTROL: old root {r} is not detected"
  -- NEGATIVE CONTROL: a scan with an empty forbidden set finds nothing (the detector is the set, not an artifact)
  let sNone := scan env {} #[``Tools.ShippingGen5ConstValueES.cvlsks_functional]
  unless sNone.violations.isEmpty do throwError "CONTROL: empty forbidden set reports hits"
  -- REQUIRED: the final roots and the consumers do not reach an old carrier
  unless sf.violations.isEmpty do
    throwError "FINAL ROOTS reach old carriers: {sf.violations.toList.take 5 |>.map (fun (n, p) => (n, p.take 8))}"
  unless sc.violations.isEmpty do
    throwError "CONSUMERS reach old carriers: {sc.violations.toList.take 5 |>.map (fun (n, p) => (n, p.take 8))}"
  let perOld := so.toList.map (fun (r, s) => s!"{r}: {show' s}")
  logInfo m!"CVFINAL SCAN: {old.size} old carrier inductives ({(names.toArray.qsort (· < ·)).toList}); final roots ({finalRoots.size}): {show' sf}; consumers ({consumerRoots.size}): {show' sc}; controls (old roots detected): {perOld}; empty-set scan clean"

end Tests.Gen5.CVFinalScan
