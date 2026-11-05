import Lean
/-! Generator of the rows of `Tools/ShippingGen5PTCorpus.lean` (Issue sparkle-ledger-dd4-final). NOT part of the kernel-checked development: it only PRINTS Lean source, which is then committed and checked by the kernel.
usage: lake env lean --run scripts/gen5/GenPTCorpus.lean KEYS_TSV OUT_LEAN OUT_MISSING
KEYS_TSV: lines `name \t kind \t levels` (the merged raw rows of `Tests/Gen5/PrimResidueKey*.lean`, K1 keys). The environment is the import closure of `Tools.ShippingGen5PTLit`
(the same as `Tools/ShippingGen5PTCorpus.lean`): a key whose constant is not in it (declarations of the corpus modules) is `Missing`.
Rows: a constructor `c : ∀ x₁ … xₙ, R` (R : Type) becomes `.tm A₁ fun x₁ => … .ty fun xᵢ => … .done R (@c x₁ … xₙ)`; an inductive type former `I : ∀ x₁ … xₙ, Type` becomes the same with `.done (@I x₁ … xₙ)`.
A binder `A` is a type argument if `A = Type`, a term argument if `A : Type`; a Prop binder (a proof), a binder above `Type 0`, a result above `Type 0` and a recursor have NO row (Missing, with the reason). -/
open Lean Meta Elab

def lvOfStr (s : String) : Option Level :=
  match s.toNat? with
  | some n => some (Nat.repeat Level.succ n Level.zero)
  | none => none

def parseLevels (s : String) : Option (List Level) :=
  let inner := ((s.replace "[" "").replace "]" "")
  if (inner.toList.all Char.isWhitespace) then some [] else
  (inner.splitOn ",").mapM (fun t => lvOfStr (t.replace " " ""))

structure Row where
  isTy : Bool
  name : Name
  ls : List Nat
  kinds : List Bool
  src : String

def sortLevel? (t : Expr) : MetaM (Option Level) := do
  let s ← whnf (← inferType t)
  match s with
  | .sort l => return some l.normalize
  | _ => return none

def isNum (l : Level) (n : Nat) : Bool := l.normalize == Nat.repeat Level.succ n Level.zero

def sanitize (n : Name) : String := toString n

partial def genGo (isTy : Bool) (c : Name) (ls : List Level) (e : Expr) (i : Nat) (names : Array String) (kinds : List Bool) (openers : Array String) :
    MetaM (Except String (List Bool × String)) := do
  let e ← whnfD e   -- expose a Pi
  match e with
  | .forallE _ A B bi =>
    let some s := (← sortLevel? A) | return .error "binder type is not a type"
    let x := s!"x{i}"
    let aStr := toString (← ppExpr A)
    let op := if isTy then "TyTele" else "TmTele"
    if (← whnfR A) == Expr.sort (Level.succ Level.zero) then
      withLocalDecl (Name.mkSimple x) bi A fun fv =>
        genGo isTy c ls (B.instantiate1 fv) (i + 1) (names.push x) (kinds ++ [false]) (openers.push s!"{op}.ty fun ({x} : Type) =>")
    else if isNum s 1 then
      withLocalDecl (Name.mkSimple x) bi A fun fv =>
        genGo isTy c ls (B.instantiate1 fv) (i + 1) (names.push x) (kinds ++ [true]) (openers.push s!"{op}.tm ({aStr}) fun ({x} : {aStr}) =>")
    else if isNum s 0 then return .error "proof binder (a Prop argument has no Dyn form)"
    else return .error "binder above Type 0 (a motive / universe-valued argument has no Arg form)"
  | R =>
    let some s := (← sortLevel? R) | return .error "result is not a type"
    let args := " ".intercalate names.toList
    let head := if ls.isEmpty then s!"@{c}" else s!"@{c}.\{{", ".intercalate (ls.map (fun l => toString l.normalize))}}"
    if isTy then
      if (← whnfR R) == Expr.sort (Level.succ Level.zero) then
        return .ok (kinds, "(" ++ " ".intercalate (openers.toList ++ [s!"TyTele.done ({head} {args})"]) ++ ")")
      else return .error "inductive family not in Type 0 (Prop or Type u, u > 0)"
    else
      if isNum s 1 then
        let Rs := toString (← ppExpr R)
        return .ok (kinds, "(" ++ " ".intercalate (openers.toList ++ [s!"TmTele.done ({Rs}) ({head} {args})"]) ++ ")")
      else return .error "result type above Type 0 (or a Prop)"

def genKey (isTy : Bool) (c : Name) (ls : List Level) : MetaM (Except String (List Bool × String)) := do
  let some ci := (← getEnv).find? c | return .error "constant not in the import closure of Tools (declaration of a corpus module)"
  if ci.levelParams.length != ls.length then return .error "level arity mismatch"
  genGo isTy c ls (ci.type.instantiateLevelParams ci.levelParams ls) 1 #[] [] #[]

unsafe def main (args : List String) : IO UInt32 := do
  let [keysPath, outPath, missPath] := args | IO.eprintln "usage: KEYS_TSV OUT_LEAN OUT_MISSING"; return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Tools.ShippingGen5PTLit }] {} 0
  let lines := (← IO.FS.readFile keysPath).splitOn "\n" |>.filter (· ≠ "")
  let mut tysRows : Array String := #[]
  let mut tmsRows : Array String := #[]
  let mut missing : Array String := #[]
  let mut nTy := 0; let mut nTm := 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default, options := Options.empty |>.setBool `pp.fullNames true |>.setBool `pp.universes true }
  for l in lines do
    match l.splitOn "\t" with
    | [n, kind, lv] =>
      let c := n.toName
      let some ls := parseLevels lv | missing := missing.push s!"{n}\t{kind}\t{lv}\tlevel list is not numerals"; continue
      let lsN := ls.map (fun l => (l.normalize.getOffset))
      if kind == "rec" then missing := missing.push s!"{n}\t{kind}\t{lv}\trecursor: its motive is a function into a Sort (no Arg form; Dyn.ty : Type)"; continue
      if kind != "ctor" && kind != "induct" then missing := missing.push s!"{n}\t{kind}\t{lv}\tkind {kind}"; continue
      let isTy := kind == "induct"
      let act : MetaM (Except String (List Bool × String)) := genKey isTy c ls
      let r : Except String (Except String (List Bool × String)) ←
        try
          let (x, _) ← (act.run' : CoreM _).toIO ctx { env := env }
          pure (.ok x)
        catch ex => pure (.error (toString ex))
      match r with
      | .ok (.ok (ks, src)) =>
        let ksS := "[" ++ ", ".intercalate (ks.map toString) ++ "]"
        let lsS := "[" ++ ", ".intercalate (lsN.map toString) ++ "]"
        if isTy then
          nTy := nTy + 1
          tysRows := tysRows.push s!"  (`{n}, {lsS}, ⟨{ksS}, {src}⟩)"
        else
          nTm := nTm + 1
          tmsRows := tmsRows.push s!"  (`{n}, {lsS}, ⟨{ksS}, {src}⟩)"
      | .ok (.error e) => missing := missing.push s!"{n}\t{kind}\t{lv}\t{e}"
      | .error ex => missing := missing.push s!"{n}\t{kind}\t{lv}\tgenerator exception: {ex}"
    | _ => pure ()
  let out := s!"-- GENERATED by scripts/gen5/GenPTCorpus.lean from the K1 key list: {nTy} type-former rows, {nTm} term rows\n" ++
    s!"def tysTable : List (Name × List Nat × (ks : List Bool) × TyTele ks) := [\n" ++ ",\n".intercalate tysRows.toList ++ "\n]\n\n" ++
    s!"def tmsTable : List (Name × List Nat × (ks : List Bool) × TmTele ks) := [\n" ++ ",\n".intercalate tmsRows.toList ++ "\n]\n"
  IO.FS.writeFile outPath out
  IO.FS.writeFile missPath ("\n".intercalate missing.toList ++ "\n")
  IO.println s!"type rows {nTy}, term rows {nTm}, missing {missing.size}"
  return 0
