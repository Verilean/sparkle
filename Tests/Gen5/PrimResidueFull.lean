import Lean
import Sparkle
import Tests.AllTests
/-! # Residue of the `ConstValueE` primitive table over the WHOLE imported corpus (D.D-4, issue sparkle-ledger-dd4-res)
Measurement only; `Tests.Gen5.PrimResidueCount` (59-declaration sample) is untouched.
Roots: every definition `X` of the environment of `Tests.AllTests` that carries a route marker of the compiler's
output — `X.machine_source` (machine), `X.gateValue` (gate), a `X.gate_design*`/`X.machine_design*`/`X.design_*`
constant (design); `@[hardware_module]` definitions without a marker are reported as the route `tagged`.
For each root every `defnInfo` is unfolded transitively (a theorem-headed application is not entered); the
non-unfoldable constants reached (constructor, recursor, inductive type former, quot, opaque, axiom) are the residue.
Output: `logInfo` aggregates; raw rows go to `$KJOB_REPORT_PATH.full.*` if set.  No theorem, no sorry. -/
open Lean Meta Elab Command

namespace Tests.Gen5.PrimResidueFull

inductive Kind | ctor | recur | quot | opaqueExt | opaquePlain | typeFormer | axiom
  deriving BEq, Repr, Hashable, Inhabited

def Kind.label : Kind → String
  | .ctor => "constructor" | .recur => "recursor" | .quot => "quot" | .opaqueExt => "opaque/extern"
  | .opaquePlain => "opaque(plain)" | .typeFormer => "type-former" | .axiom => "axiom"

def Kind.ofConst? (env : Environment) (n : Name) : Option Kind :=
  match env.find? n with
  | some (.ctorInfo _) => some .ctor
  | some (.recInfo _) => some .recur
  | some (.quotInfo _) => some .quot
  | some (.inductInfo _) => some .typeFormer
  | some (.axiomInfo _) => some .axiom
  | some (.opaqueInfo _) => some (if (Compiler.getImplementedBy? env n).isSome || isExtern env n then .opaqueExt else .opaquePlain)
  | _ => none

/-- Number of arguments after which a residue constant is fully applied. -/
def arity (env : Environment) (n : Name) : Nat :=
  match env.find? n with
  | some (.ctorInfo c) => c.numParams + c.numFields
  | some (.recInfo r) => r.numParams + r.numMotives + r.numMinors + r.numIndices + 1
  | some (.inductInfo i) => i.numParams + i.numIndices
  | _ => 0

structure Sites where
  /-- partial applications per residue constant (distinct unfolded definitions' sites). -/
  partialUse : NameMap Nat := {}
  fullUse : NameMap Nat := {}
  /-- recursor sites by (recursor, motive level class, major class) -/
  recSites : Array (Name × String × String) := #[]
  recSiteDefs : Array Name := #[]
  /-- type-abstractions: lambdas whose binder is a Sort/type-former, at the head telescope of a definition
  (rank-1 polymorphism) and nested (inside the body or as an argument). -/
  tyLamHead : Nat := 0
  tyLamNested : Nat := 0
  /-- definitions (unfolded) with a head type-abstraction / with a nested one -/
  defsHeadPoly : Nat := 0
  defsNestedPoly : Nat := 0

def isSortLike : Expr → Bool
  | .sort _ => true
  | .forallE _ _ b _ => isSortLike b
  | .mdata _ e => isSortLike e
  | _ => false

def levelClass (l : Level) : String :=
  let l := l.normalize
  if l.isZero then "closed:Prop(0)"
  else if l.hasParam || l.hasMVar then "mentions-level-param"
  else match l.toNat with
    | some 1 => "closed:Type0(1)"
    | some k => s!"closed:{k}"
    | none => "closed:other"

partial def majorClass (e : Expr) : String :=
  match e with
  | .mdata _ b => majorClass b
  | .bvar _ => "bvar"
  | .lit _ => "literal"
  | .proj .. => "proj"
  | .lam .. => "lambda"
  | .app .. | .const .. =>
    match e.getAppFn with
    | .const n _ => s!"head-const"  -- refined by the caller
    | .bvar _ => "bvar-app"
    | _ => "other-app"
  | _ => "other"

/-- All constants referenced by a definition value, not entering theorem-headed applications. -/
partial def consts (env : Environment) (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app .. =>
    let f := e.getAppFn
    match f with
    | .const n _ =>
      if (env.find? n).any (·.isTheorem) then acc
      else e.getAppArgs.foldl (fun a x => consts env x a) (acc.insert n)
    | _ => e.getAppArgs.foldl (fun a x => consts env x a) (consts env f acc)
  | .lam _ t b _ | .forallE _ t b _ => consts env b (consts env t acc)
  | .letE _ t v b _ => consts env b (consts env v (consts env t acc))
  | .mdata _ b | .proj _ _ b => consts env b acc
  | _ => acc

def headLams : Expr → Nat
  | .lam _ _ b _ => headLams b + 1
  | .mdata _ e => headLams e
  | _ => 0

/-- Site statistics of ONE definition value (called once per distinct unfolded definition).
`depth` = binders entered; `hn` = number of leading lambdas of the value (the definition's parameters). -/
partial def sites (env : Environment) (hn : Nat) (e : Expr) (s : Sites) (depth : Nat) : Sites :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n ls =>
      if (env.find? n).any (·.isTheorem) then s
      else Id.run do
        let mut s := s
        if let some k := Kind.ofConst? env n then
          let a := arity env n
          if args.size < a then s := { s with partialUse := s.partialUse.insert n ((s.partialUse.getD n 0) + 1) }
          else s := { s with fullUse := s.fullUse.insert n ((s.fullUse.getD n 0) + 1) }
          if k == .recur then
            if let some (.recInfo rv) := env.find? n then
              let indLv := ((env.find? rv.getMajorInduct).map (·.levelParams.length)).getD 0
              let lc := if rv.levelParams.length > indLv then (match ls.head? with | some l => levelClass l | none => "?") else "Prop-only-elim"
              let mi := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
              let mc :=
                if h : mi < args.size then
                  let m := args[mi]
                  match majorClass m with
                  | "head-const" =>
                    match m.getAppFn with
                    | .const c _ => (match env.find? c with
                        | some (.ctorInfo _) => "ctor-app"
                        | some (.defnInfo _) => "defn-app"
                        | some (.recInfo _) => "rec-app"
                        | some (.thmInfo _) => "proof-app"
                        | _ => "other-const-app")
                    | _ => "?"
                  | "bvar" =>
                    match m with
                    | .bvar i => if i < depth then (if depth - 1 - i < hn then "bvar:def-parameter" else "bvar:inner-binder") else "bvar:loose"
                    | _ => "bvar"
                  | x => x
                else "partial(no major)"
              s := { s with recSites := s.recSites.push (n, lc, mc) }
        return args.foldl (fun a x => sites env hn x a depth) s
    | _ => args.foldl (fun a x => sites env hn x a depth) (sites env hn f s depth)
  | .lam _ t b _ =>
    let s := if isSortLike t then
        (if depth < hn then { s with tyLamHead := s.tyLamHead + 1 } else { s with tyLamNested := s.tyLamNested + 1 })
      else s
    sites env hn b (sites env hn t s depth) (depth + 1)
  | .forallE _ t b _ => sites env hn b (sites env hn t s depth) (depth + 1)
  | .letE _ t v b _ => sites env hn b (sites env hn v (sites env hn t s depth) depth) (depth + 1)
  | .mdata _ b | .proj _ _ b => sites env hn b s depth
  | _ => s

structure Root where
  name : Name
  routes : List String

def routeOf (last : String) : Option String :=
  if last == "machine_source" then some "machine"
  else if last == "gateValue" then some "gate"
  else if last.startsWith "gate_design" || last.startsWith "machine_design" || last.startsWith "design_" then some "design"
  else none

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]?).map toString |>.getD "?"
  | none => "<local>"

def isUserModule (m : String) : Bool :=
  m.startsWith "Tests." || m.startsWith "Examples" || m.startsWith "IP." || m.startsWith "Tools.Test" || m == "<local>"

elab "#prim_residue_full" : command => do
  let env ← getEnv
  -- roots with routes
  let mut rootRoutes : NameMap (List String) := {}
  for (n, _) in env.constants.toList do
    match n with
    | .str p s =>
      if let some r := routeOf s then
        if (env.find? p).any (·.isDefinition) then
          let cur := rootRoutes.getD p []
          unless cur.contains r do rootRoutes := rootRoutes.insert p (r :: cur)
    | _ => pure ()
  for (n, ci) in env.constants.toList do
    if ci.isDefinition && Sparkle.Compiler.isHardwareModule env n && !(rootRoutes.contains n) then
      rootRoutes := rootRoutes.insert n ["tagged"]
  -- roots named by `#synthesizeVerilog X`-like commands in the corpus files (list: `$KJOB_REPORT_PATH.tops`, lines `Module<TAB>name`)
  let mut topsTotal := 0
  let mut topsResolved := 0
  let mut topsUnresolved : Array String := #[]
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    if (← System.FilePath.pathExists (path ++ ".tops")) then
      let lines ← IO.FS.lines (path ++ ".tops")
      -- index the definitions of the modules named in the list (module -> definitions), one pass over the environment
      let mut wanted : Std.HashSet String := {}
      for l in lines do
        match l.splitOn "\t" with
        | [m, _] => wanted := wanted.insert m
        | _ => pure ()
      let mut byMod : Std.HashMap String (Array Name) := {}
      for (n, ci) in env.constants.toList do
        if ci.isDefinition then
          match env.getModuleIdxFor? n with
          | some i =>
            let m := (env.header.moduleNames[i.toNat]?).map toString |>.getD "?"
            if wanted.contains m then byMod := byMod.insert m ((byMod.getD m #[]).push n)
          | none => pure ()
      for l in lines do
        match l.splitOn "\t" with
        | [m, nm] =>
          topsTotal := topsTotal + 1
          let cands := (byMod.getD m #[]).toList.filter fun d => d.toString == nm || d.toString.endsWith ("." ++ nm)
          if cands.isEmpty then
            let inEnv := env.header.moduleNames.any (fun x => toString x == m)
            topsUnresolved := topsUnresolved.push (s!"{m}\t{nm}\t" ++ (if inEnv then "module-imported-name-not-found" else "module-not-imported"))
          else
            topsResolved := topsResolved + 1
            for d in cands do
              let cur := rootRoutes.getD d []
              unless cur.contains "synth" do rootRoutes := rootRoutes.insert d ("synth" :: cur)
        | _ => pure ()
  let roots := rootRoutes.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  -- direct constants cache and per-root closure
  let mut direct : NameMap (Array Name) := {}
  let mut siteAcc : Sites := {}
  let mut defsSeen : NameSet := {}
  let mut perRoot : Array (Name × List String × NameSet × Nat) := #[]
  for (r, rts) in roots do
    let mut seen : NameSet := {}
    let mut todo : Array Name := #[r]
    let mut res : NameSet := {}
    let mut unfolded := 0
    while h : todo.size > 0 do
      let n := todo.back
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        unfolded := unfolded + 1
        let cs ← match direct.find? n with
          | some cs => pure cs
          | none =>
            let cs := (consts env d.value {}).toList.toArray
            direct := direct.insert n cs
            pure cs
        unless defsSeen.contains n do
          defsSeen := defsSeen.insert n
          let before := siteAcc
          let s2 := sites env (headLams d.value) d.value siteAcc 0
          let s2 := { s2 with recSiteDefs := s2.recSiteDefs ++ (Array.replicate (s2.recSites.size - siteAcc.recSites.size) n) }
          let headPoly := s2.tyLamHead > before.tyLamHead
          let nestPoly := s2.tyLamNested > before.tyLamNested
          siteAcc := { s2 with defsHeadPoly := s2.defsHeadPoly + (if headPoly then 1 else 0),
                               defsNestedPoly := s2.defsNestedPoly + (if nestPoly then 1 else 0) }
        for c in cs do todo := todo.push c
      | some (.thmInfo _) => pure ()
      | some _ => if (Kind.ofConst? env n).isSome then res := res.insert n
      | none => pure ()
    perRoot := perRoot.push (r, rts, res, unfolded)
  -- aggregate per residue constant
  let mut byConst : NameMap (Nat × List String × Array Name) := {}   -- (#roots, routes-set, examples)
  let mut routeCounts : NameMap (NameMap Nat) := {}
  for (r, rts, res, _) in perRoot do
    for c in res.toList do
      let (k, rs, ex) := byConst.getD c (0, [], #[])
      let rs' := rts.foldl (fun a x => if a.contains x then a else x :: a) rs
      byConst := byConst.insert c (k + 1, rs', if ex.size < 3 then ex.push r else ex)
  -- aggregate counts
  let allRes := byConst.toList.toArray
  let kindCount (k : Kind) := (allRes.filter (fun (n, _) => Kind.ofConst? env n == some k)).size
  let routeNames := ["machine", "gate", "design", "tagged", "synth"]
  let mut msg := s!"FULL corpus scan of the Tests.AllTests environment (IP/ and Examples/ modules it imports are included; target-only roots are NOT)\n"
  msg := msg ++ s!"synthesize-command names: {topsTotal}, resolved to a definition of their own module: {topsResolved}, unresolved: {topsUnresolved.size} (module not imported: {(topsUnresolved.filter (·.endsWith "module-not-imported")).size}, module imported but name not found: {(topsUnresolved.filter (·.endsWith "name-not-found")).size})\n"
  msg := msg ++ s!"roots (definitions with a route marker or @[hardware_module]): {roots.size}\n"
  for rt in routeNames do
    msg := msg ++ s!"  route {rt}: {(roots.filter (fun (_, rs) => rs.contains rt)).size}\n"
  msg := msg ++ s!"distinct residue constants: {allRes.size}\n"
  for k in [Kind.ctor, .recur, .quot, .opaqueExt, .opaquePlain, .typeFormer, .axiom] do
    msg := msg ++ s!"  {k.label}: {kindCount k}\n"
  -- library vs user
  let mut lib := 0
  let mut usr := 0
  for (n, _) in allRes do
    if isUserModule (moduleOf env n) then usr := usr + 1 else lib := lib + 1
  msg := msg ++ s!"library/core constants: {lib}; user (Tests/Examples/IP/local) constants: {usr}\n"
  -- per route residue (distinct)
  for rt in routeNames do
    let mut s : NameSet := {}
    for (_, rts, res, _) in perRoot do
      if rts.contains rt then for c in res.toList do s := s.insert c
    let ks := [Kind.ctor, .recur, .typeFormer].map fun k => (s.toList.filter (fun n => Kind.ofConst? env n == some k)).length
    msg := msg ++ s!"  route {rt}: distinct residue {s.size} (ctor {ks[0]!}, rec {ks[1]!}, type {ks[2]!})\n"
  -- sites
  let totalPartial := siteAcc.partialUse.toList.foldl (fun a (_, v) => a + v) 0
  let totalFull := siteAcc.fullUse.toList.foldl (fun a (_, v) => a + v) 0
  msg := msg ++ s!"unfolded distinct definitions: {defsSeen.toList.length}\n"
  msg := msg ++ s!"residue sites (distinct unfolded definitions): full {totalFull}, PARTIAL {totalPartial} (constants with a partial site: {siteAcc.partialUse.toList.length})\n"
  msg := msg ++ s!"type-abstraction lambdas: head-telescope {siteAcc.tyLamHead}, nested/argument {siteAcc.tyLamNested}; definitions with head type-abstraction {siteAcc.defsHeadPoly}, with a nested one {siteAcc.defsNestedPoly}\n"
  -- recursor site classes
  let mut recStat : NameMap Nat := {}
  let mut lvStat : Std.HashMap String Nat := {}
  let mut majStat : Std.HashMap String Nat := {}
  for (_, lc, mc) in siteAcc.recSites do
    lvStat := lvStat.insert lc (lvStat.getD lc 0 + 1)
    majStat := majStat.insert mc (majStat.getD mc 0 + 1)
  for (n, _, _) in siteAcc.recSites do recStat := recStat.insert n (recStat.getD n 0 + 1)
  msg := msg ++ s!"recursor sites: {siteAcc.recSites.size} over {recStat.toList.length} recursors\n  motive level: {lvStat.toList.map (fun (k, v) => s!"{k}={v}")}\n  major premise: {majStat.toList.map (fun (k, v) => s!"{k}={v}")}\n"
  -- coverage: roots whose residue has no recursor / only ctor+type
  let noRec := (perRoot.filter fun (_, _, res, _) => !res.toList.any (fun n => Kind.ofConst? env n == some .recur)).size
  msg := msg ++ s!"roots with NO recursor in the residue: {noRec} / {perRoot.size}\n"
  logInfo msg
  if let some path ← (IO.getEnv "KJOB_REPORT_PATH") then
    -- raw: per constant
    let rows := allRes.qsort (fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1.toString < b.1.toString))
    let mut out := "name\tkind\tarity\tmodule\troots\troutes\tpartial\tfull\texamples\ttype\n"
    let tys ← liftTermElabM do
      let mut o : Array String := #[]
      for (n, _) in rows do
        let t ← (do let some ci := env.find? n | return ""
                    let s ← ppExpr ci.type
                    return (toString s).replace "\n" " ")
        o := o.push t
      return o
    let mut i := 0
    for (n, (k, rs, ex)) in rows do
      let kd := ((Kind.ofConst? env n).map (·.label)).getD "?"
      out := out ++ s!"{n}\t{kd}\t{arity env n}\t{moduleOf env n}\t{k}\t{",".intercalate rs}\t{siteAcc.partialUse.getD n 0}\t{siteAcc.fullUse.getD n 0}\t{",".intercalate (ex.toList.map toString)}\t{tys[i]!}\n"
      i := i + 1
    IO.FS.writeFile (path ++ ".full.consts") out
    let mut rr := "root\troutes\tunfolded\tresidue\tnrec\tresidue-names\n"
    for (r, rts, res, u) in perRoot do
      let nrec := (res.toList.filter (fun n => Kind.ofConst? env n == some .recur)).length
      rr := rr ++ s!"{r}\t{",".intercalate rts}\t{u}\t{res.size}\t{nrec}\t{" ".intercalate (res.toList.map toString)}\n"
    IO.FS.writeFile (path ++ ".full.roots") rr
    let mut rs := "rec\tmotive-level\tmajor\n"
    let mut ri := 0
    for (n, lc, mc) in siteAcc.recSites do
      rs := rs ++ s!"{n}\t{lc}\t{mc}\t{siteAcc.recSiteDefs[ri]!}\n"
      ri := ri + 1
    IO.FS.writeFile (path ++ ".full.unresolved") ("\n".intercalate topsUnresolved.toList)
    IO.FS.writeFile (path ++ ".full.recsites") rs

#prim_residue_full

end Tests.Gen5.PrimResidueFull
