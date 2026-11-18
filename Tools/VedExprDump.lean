import Lean

/-! Diagnostic only (never changes behaviour): write a closed kernel term `T`/`V` (with the
definitions of the constants that come from the current file) as a sharing-preserving text file and
read it back in another file, to re-run the kernel check standalone. -/
namespace Tools.VedExprDump
open Lean

def encName (n : Name) : String :=
  "\x01".intercalate (n.components.map fun
    | .str _ s => "s:" ++ s
    | .num _ k => "n:" ++ toString k
    | .anonymous => "")

def decName (s : String) : Name :=
  if s.isEmpty then .anonymous else
  (s.splitOn "\x01").foldl (init := Name.anonymous) fun n c =>
    if c.startsWith "n:" then .num n (c.drop 2).toString.toNat! else .str n (c.drop 2).toString

def encLevel : Level → String
  | .zero => "Z"
  | .succ l => "S\x02" ++ encLevel l
  | .max a b => "M\x02" ++ encLevel a ++ "\x02" ++ encLevel b
  | .imax a b => "I\x02" ++ encLevel a ++ "\x02" ++ encLevel b
  | .param n => "P\x02" ++ encName n
  | .mvar _ => "Z"

/-- parse one level from a token list, return the rest -/
partial def decLevelAux : List String → Level × List String
  | "Z" :: r => (.zero, r)
  | "S" :: r => let (l, r) := decLevelAux r; (.succ l, r)
  | "M" :: r => let (a, r) := decLevelAux r; let (b, r) := decLevelAux r; (.max a b, r)
  | "I" :: r => let (a, r) := decLevelAux r; let (b, r) := decLevelAux r; (.imax a b, r)
  | "P" :: n :: r => (.param (decName n), r)
  | _ => (.zero, [])

def decLevel (s : String) : Level := (decLevelAux (s.splitOn "\x02")).1

def biNat : BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
def natBi : Nat → BinderInfo
  | 1 => .implicit | 2 => .strictImplicit | 3 => .instImplicit | _ => .default

def hexOf (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let h := (Nat.toDigits 16 b.toNat); (if h.length < 2 then "0" else "") ++ String.ofList h)

def hexVal (c : Char) : Nat :=
  if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 48

def unhex (s : String) : String :=
  let cs := s.toList.toArray
  let bs := (List.range (cs.size / 2)).map fun i =>
    (hexVal cs[2*i]! * 16 + hexVal cs[2*i+1]!)
  String.fromUTF8! ⟨(bs.map (·.toUInt8)).toArray⟩

structure Pool where
  cache : Std.HashMap USize Nat := {}
  lines : Array String := #[]

unsafe def encU (pool : IO.Ref Pool) (e : Expr) : IO Nat := do
  let rec go (e : Expr) : IO Nat := do
    let k := ptrAddrUnsafe e
    if let some i := (← pool.get).cache[k]? then return i
    let line ← match e with
      | .bvar i => pure s!"B\t{i}"
      | .sort l => pure s!"S\t{encLevel l}"
      | .const n ls => pure s!"C\t{encName n}\t{"\x03".intercalate (ls.map encLevel)}"
      | .app f a => do let f ← go f; let a ← go a; pure s!"A\t{f}\t{a}"
      | .lam n t b bi => do let t ← go t; let b ← go b; pure s!"L\t{encName n}\t{biNat bi}\t{t}\t{b}"
      | .forallE n t b bi => do
        let t ← go t; let b ← go b; pure s!"P\t{encName n}\t{biNat bi}\t{t}\t{b}"
      | .letE n t v b nd => do
        let t ← go t; let v ← go v; let b ← go b; pure s!"E\t{encName n}\t{t}\t{v}\t{b}\t{nd}"
      | .lit (.natVal n) => pure s!"N\t{n}"
      | .lit (.strVal s) => pure s!"T\t{hexOf s}"
      | .mdata _ b => do return (← go b)
      | .proj s i b => do let b ← go b; pure s!"J\t{encName s}\t{i}\t{b}"
      | .fvar _ => throw (IO.userError "dump: fvar")
      | .mvar _ => throw (IO.userError "dump: mvar")
    let p ← pool.get
    let id := p.lines.size
    pool.set { cache := p.cache.insert k id, lines := p.lines.push line }
    return id
  go e

@[implemented_by encU] opaque enc (pool : IO.Ref Pool) (e : Expr) : IO Nat

/-- Write `ty`/`val` and the local (not imported) constants they use. -/
def dump (env : Environment) (path : String) (ty val : Expr) : IO Unit := do
  let pool ← IO.mkRef ({} : Pool)
  let tId ← enc pool ty
  let vId ← enc pool val
  let mut decls : Array String := #[]
  let mut done : Std.HashSet Name := {}
  let scanNew (from' : Nat) (lines : Array String) : Array Name := Id.run do
    let mut r := #[]
    for i in [from':lines.size] do
      let l := lines[i]!
      if l.startsWith "C\t" then
        let n := decName ((l.splitOn "\t")[1]!)
        if (env.getModuleIdxFor? n).isNone then r := r.push n
    r
  let mut pending := scanNew 0 (← pool.get).lines
  let mut order : Array Name := #[]
  -- discovery (BFS), emission order fixed afterwards by sorting on discovery dependencies
  let mut deps : Std.HashMap Name (Array Name) := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if done.contains n then continue
    done := done.insert n
    order := order.push n
    let some ci := env.find? n | continue
    let before := (← pool.get).lines.size
    let tid ← enc pool ci.type
    let vid ← match ci with
      | .defnInfo d => enc pool d.value
      | .thmInfo d => enc pool d.value
      | _ => pure 0
    let ds := scanNew before (← pool.get).lines
    deps := deps.insert n ds
    pending := pending ++ ds
    let lps := "\x03".intercalate (ci.levelParams.map encName)
    let kind ← match ci with
      | .defnInfo d =>
        let h := match d.hints with | .opaque => "o" | .abbrev => "a" | .regular k => s!"r{k}"
        pure s!"D\t{h}"
      | .thmInfo _ => pure "T\t-"
      | _ => pure s!"X\t{ci.name}"
    decls := decls.push s!"{encName n}\t{kind}\t{lps}\t{tid}\t{vid}"
  -- topological order on deps
  let mut emitted : Std.HashSet Name := {}
  let mut sorted : Array String := #[]
  let byName : Std.HashMap String String := decls.foldl (init := {}) fun m l => m.insert ((l.splitOn "\t")[0]!) l
  let rec visit (fuel : Nat) (n : Name) (emitted : Std.HashSet Name) (sorted : Array String) :
      Std.HashSet Name × Array String :=
    match fuel with
    | 0 => (emitted, sorted)
    | fuel+1 =>
      if emitted.contains n then (emitted, sorted) else
      let emitted := emitted.insert n
      let (emitted, sorted) := (deps.getD n #[]).foldl (init := (emitted, sorted)) fun (e, s) d =>
        visit fuel d e s
      match byName[encName n]? with
      | some l => (emitted, sorted.push l)
      | none => (emitted, sorted)
  for n in order do
    let (e, s) := visit 100000 n emitted sorted
    emitted := e; sorted := s
  let p ← pool.get
  let h ← IO.FS.Handle.mk path .write
  h.putStrLn s!"POOL {p.lines.size}"
  for l in p.lines do h.putStrLn l
  h.putStrLn s!"DECLS {sorted.size}"
  for l in sorted do h.putStrLn l
  h.putStrLn s!"ROOT {tId} {vId}"
  h.flush

/-- The parsed dump: pool, local declarations, root type and value. -/
structure Loaded where
  pool : Array Expr
  decls : Array (Name × String × String × List Name × Nat × Nat)
  tId : Nat
  vId : Nat

def load (path : String) : IO Loaded := do
  let ls := (← IO.FS.lines path)
  let nPool := (ls[0]!.splitOn " ")[1]!.toNat!
  let mut pool : Array Expr := Array.mkEmpty nPool
  for i in [0:nPool] do
    let f := (ls[1 + i]!).splitOn "\t"
    let g (k : Nat) : Expr := pool[(f[k]!).toNat!]!
    let e : Expr := match f[0]! with
      | "B" => .bvar f[1]!.toNat!
      | "S" => .sort (decLevel f[1]!)
      | "C" => .const (decName f[1]!) (if f[2]!.isEmpty then [] else (f[2]!.splitOn "\x03").map decLevel)
      | "A" => .app (g 1) (g 2)
      | "L" => .lam (decName f[1]!) (g 3) (g 4) (natBi f[2]!.toNat!)
      | "P" => .forallE (decName f[1]!) (g 3) (g 4) (natBi f[2]!.toNat!)
      | "E" => .letE (decName f[1]!) (g 2) (g 3) (g 4) (f[5]! == "true")
      | "N" => .lit (.natVal f[1]!.toNat!)
      | "T" => .lit (.strVal (unhex f[1]!))
      | "J" => .proj (decName f[1]!) f[2]!.toNat! (g 3)
      | _ => .bvar 0
    pool := pool.push e
  let nD := (ls[1 + nPool]!.splitOn " ")[1]!.toNat!
  let mut decls := #[]
  for i in [0:nD] do
    let f := ls[2 + nPool + i]!.splitOn "\t"
    let lps := if f[3]!.isEmpty then [] else (f[3]!.splitOn "\x03").map decName
    decls := decls.push (decName f[0]!, f[1]!, f[2]!, lps, f[4]!.toNat!, f[5]!.toNat!)
  let r := (ls[2 + nPool + nD]!.splitOn " ")
  return { pool, decls, tId := r[1]!.toNat!, vId := r[2]!.toNat! }

end Tools.VedExprDump
