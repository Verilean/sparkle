import Lean
import Sparkle
/-! # Residue scan over ONE environment (D.D-4, issue sparkle-ledger-dd4-res, revision 2)
The functions of `Tests.Gen5.PrimResidueFull` (kept unchanged) without its `Tests.AllTests` import, so that a scan can run in
any environment: AllTests, AllTests + one more module, or one module alone (modules that cannot share an environment).
Measurement only. No theorem, no sorry. Configuration by environment variables (no source-tree output):
* `PRIM_RES_ROOTS`  file, one definition name per line: roots named by the compiler's own log (`declName resolved: X`);
* `PRIM_RES_MODS`   comma list of modules whose marker / `@[hardware_module]` definitions are roots; `*` = every module;
* `PRIM_RES_OUT`    output prefix: writes `<prefix>.roots` and `<prefix>.consts`;
* `PRIM_RES_ONLY`   if set, ONLY the roots of the names file are used (no marker / tagged roots). -/
open Lean Meta Elab Command

namespace Tests.Gen5.PrimResidueLib

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

/-- Scan the residue of the roots selected by the environment variables; one line per root, one line per constant. -/
def scanEnv (env : Environment) (rootNames : Array (Name × List String)) (mods : List String) (onlyNames : Bool) :
    IO (Array (Name × List String × NameSet × Nat) × Sites) := do
  let allMods := mods.contains "*"
  let mut rootRoutes : NameMap (List String) := {}
  unless onlyNames do
    for (n, _) in env.constants.toList do
      match n with
      | .str p s =>
        if let some r := routeOf s then
          if (env.find? p).any (·.isDefinition) && (allMods || mods.contains (moduleOf env p)) then
            let cur := rootRoutes.getD p []
            unless cur.contains r do rootRoutes := rootRoutes.insert p (r :: cur)
      | _ => pure ()
    for (n, ci) in env.constants.toList do
      if ci.isDefinition && (allMods || mods.contains (moduleOf env n)) && Sparkle.Compiler.isHardwareModule env n
          && !(rootRoutes.contains n) then
        rootRoutes := rootRoutes.insert n ["tagged"]
  for (n, tags) in rootNames do
    if (env.find? n).any (·.isDefinition) then
      let mut cur := rootRoutes.getD n []
      for t in "synth" :: tags do
        unless cur.contains t do cur := t :: cur
      rootRoutes := rootRoutes.insert n cur
  let roots := rootRoutes.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
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
          let s2 := { s2 with recSiteDefs := s2.recSiteDefs ++ (Array.replicate (s2.recSites.size - before.recSites.size) n) }
          siteAcc := { s2 with defsHeadPoly := s2.defsHeadPoly + (if s2.tyLamHead > before.tyLamHead then 1 else 0),
                               defsNestedPoly := s2.defsNestedPoly + (if s2.tyLamNested > before.tyLamNested then 1 else 0) }
        for c in cs do todo := todo.push c
      | some (.thmInfo _) => pure ()
      | some _ => if (Kind.ofConst? env n).isSome then res := res.insert n
      | none => pure ()
    perRoot := perRoot.push (r, rts, res, unfolded)
  return (perRoot, siteAcc)

elab "#prim_residue_scan" : command => do
  let env ← getEnv
  let some out ← IO.getEnv "PRIM_RES_OUT" | throwError "PRIM_RES_OUT not set"
  let mods := ((← IO.getEnv "PRIM_RES_MODS").getD "").splitOn "," |>.filter (· ≠ "")
  let onlyNames := (← IO.getEnv "PRIM_RES_ONLY").isSome
  let mut names : Array (Name × List String) := #[]
  let mut missing : Array String := #[]
  if let some f ← IO.getEnv "PRIM_RES_ROOTS" then
    for l in ← IO.FS.lines f do
      let l := l.trimAscii.toString
      if l.isEmpty then continue
      let n := l.toName
      if (env.find? n).any (·.isDefinition) then names := names.push (n, []) else missing := missing.push l
  -- roots named by the compiler's own profile log (slice of this run): every declaration whose synthesis
  -- got past the dispatch, with the front end it took
  if let some lf ← IO.getEnv "PRIM_RES_PROFILE" then
    let off := ((← IO.getEnv "PRIM_RES_PROFOFF").bind String.toNat?).getD 0
    if (← System.FilePath.pathExists lf) then
      let bytes ← IO.FS.readBinFile lf
      let txt := (String.fromUTF8? (bytes.extract off bytes.size)).getD ""
      let mut routes : Std.HashMap String (List String) := {}
      let mut order : Array String := #[]
      let mut entered : Std.HashSet String := {}
      for l in txt.splitOn "\n" do
        if l.startsWith "[profile] declName resolved: " then
          let n := (l.drop 29).toString.trimAscii.toString
          unless routes.contains n do
            routes := routes.insert n []
            order := order.push n
          routes := routes.insert n (if (routes.getD n []).contains "cmd" then routes.getD n [] else "cmd" :: routes.getD n [])
        else if l.startsWith "[profile] synthesizeCombinational " then
          match (l.drop 34).toString.splitOn " " with
          | n :: rest =>
            let what := " ".intercalate rest
            let r? : Option String :=
              if what == "certified front end" then some "S0"
              else if what == "mixed certified front end" then some "mixed"
              else if what == "machine certified front end" then some "machine"
              else if what == "MEMO HIT" then some "memo"
              else if what.startsWith "starting" then some "legacy"
              else none
            if what == "entering" then entered := entered.insert n
            if let some r := r? then
              unless routes.contains n do
                routes := routes.insert n []
                order := order.push n
              let cur := routes.getD n []
              unless cur.contains r do routes := routes.insert n (r :: cur)
          | _ => pure ()
      let mut prof := "name\troutes\tstatus\n"
      for n in order do
        let rs := routes.getD n []
        let nm := n.toName
        let isDef := (env.find? nm).any (·.isDefinition)
        let past := rs.any (· ≠ "cmd")
        prof := prof ++ s!"{n}\t{",".intercalate rs}\t{if !isDef then "not-a-definition" else if past then "ok" else "no-dispatch"}\n"
        if isDef && past then names := names.push (nm, rs.filter (· ≠ "cmd"))
        else if !isDef then missing := missing.push n
      IO.FS.writeFile (out ++ ".prof") prof
  let (perRoot, siteAcc) ← scanEnv env names mods onlyNames
  let mut rr := "root\troutes\tmodule\tunfolded\tresidue\tnrec\tresidue-names\n"
  let mut allRes : NameSet := {}
  for (r, rts, res, u) in perRoot do
    let nrec := (res.toList.filter (fun n => Kind.ofConst? env n == some .recur)).length
    rr := rr ++ s!"{r}\t{",".intercalate rts}\t{moduleOf env r}\t{u}\t{res.size}\t{nrec}\t{" ".intercalate (res.toList.map toString)}\n"
    for c in res.toList do allRes := allRes.insert c
  IO.FS.writeFile (out ++ ".roots") rr
  let mut cs := "name\tkind\tarity\tmodule\tpartial\tfull\n"
  for n in allRes.toList do
    let kd := ((Kind.ofConst? env n).map (·.label)).getD "?"
    cs := cs ++ s!"{n}\t{kd}\t{arity env n}\t{moduleOf env n}\t{siteAcc.partialUse.getD n 0}\t{siteAcc.fullUse.getD n 0}\n"
  IO.FS.writeFile (out ++ ".consts") cs
  let mut rs := "rec\tmotive-level\tmajor\tdef\n"
  let mut ri := 0
  for (n, lc, mc) in siteAcc.recSites do
    rs := rs ++ s!"{n}\t{lc}\t{mc}\t{siteAcc.recSiteDefs[ri]!}\n"
    ri := ri + 1
  IO.FS.writeFile (out ++ ".recsites") rs
  IO.FS.writeFile (out ++ ".poly") s!"tyLamHead {siteAcc.tyLamHead}\ntyLamNested {siteAcc.tyLamNested}\ndefsHeadPoly {siteAcc.defsHeadPoly}\ndefsNestedPoly {siteAcc.defsNestedPoly}\n"
  IO.FS.writeFile (out ++ ".missing") ("\n".intercalate missing.toList)
  logInfo s!"roots {perRoot.size}, distinct residue {allRes.size}, names given {names.size}, names not a definition here {missing.size}"

end Tests.Gen5.PrimResidueLib
