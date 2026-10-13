import Lean.Elab.Command
import Tests.Compiler.CacheCoherenceProbe
import Tools.ShippingModuleName

/-! # Finding H fixed: module names are injective in the declaration (ASSERTING)

WRITTEN, NOT BUILT. Imports the probe (`Tests/Compiler/CacheCoherenceProbe.lean`,
log-only, target-built) for the colliding declarations; this file THROWS
when an assertion fails.

1. The encoding table (`Sparkle.IR.ModuleName`): `#guard`s on concrete
   names — the four H cases, `.anonymous`, `.str` against `.num`, a
   component containing `.`, `_`, `$`, a non-ASCII character, an empty
   component, a keyword, a leading digit, a name written like a memory
   module, the classic `A.b_c` / `A.b.c` / `«A_b».c` / `A_b_c` family; that
   `decode` reads every row back; that the emitter's `sanitizeName` leaves
   every row unchanged and every row is a legal identifier
   (`Sparkle.IR.ModuleNames.legal`). Evaluated by the compiler, not the
   kernel; the general statements are the theorems of
   `Tools/ShippingModuleName.lean`.
2. For `nTop`, `nDirect`, `mTop`, `mmTop`: the design the real entry returns
   holds TWO different modules for the two colliding declarations, under
   two different names; each parent instantiates the one its source calls;
   the child cache the run leaves has no clash (two different declarations
   holding unequal modules of one name).

Lines: `MODNAMEINJ <top>: …` (one per top), `MODNAMEINJ TABLE: <n> rows`.

NOT established here: the simulated function (that is
`scripts/shipping-coverage/module_name_sim.sh`); cache coherence in general
(no clash in these four runs is a measurement, not the invariant). Before
the renaming these four designs were measured WRONG at the design level
and were never simulated. -/
namespace Tests.Compiler.ModuleNameInjectiveTest
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.IR.ModuleName
open Tests.Compiler.CallWidthHuntTest (Mod Dsn bs resetRefs)
open Tests.Compiler.NestedLetCacheTest (stmtStr designOf)
open Tests.Compiler.SubInstanceKeyTest (runFull instOf)
open Tests.Compiler.CacheCoherenceProbe

/-! ## 1. The table -/

def str1 (a : String) : Name := Name.mkStr Name.anonymous a
def str2 (a b : String) : Name := Name.mkStr (str1 a) b
def str3 (a b c : String) : Name := Name.mkStr (str2 a b) c

def privName : Name :=
  Name.mkStr (Name.mkStr (Name.mkNum (Name.mkStr (str1 "_private") "M") 0) "M") "f"

/-- The rows: a key and the module name it must have. -/
def table : List (Key × String) :=
  [ (.decl (str3 "Tests" "Foo" "bar"), "Tests_Foo_bar"),
    (.decl (str1 "foo"), "foo"),
    (.decl (str2 "A" "b_c"), "A_b_c"),
    (.decl (str3 "A" "b" "c"), "Sp$D$A$b$c"),
    (.decl (str2 "A_b" "c"), "Sp$D$A__b$c"),
    (.decl (str1 "A_b_c"), "Sp$D$A__b__c"),
    (.decl Name.anonymous, "Sp$D"),
    (.decl (str1 ""), "Sp$D$"),
    (.decl (str2 "A" "1"), "Sp$D$A$1"),
    (.decl (Name.mkNum (str1 "A") 1), "Sp$D$A$_1"),
    (.decl (str2 "A" "_1"), "Sp$D$A$__1"),
    (.decl (str1 "A.b"), "Sp$D$A_46_b"),
    (.decl (str2 "A" "b"), "A_b"),
    (.decl (str1 "A_b"), "Sp$D$A__b"),
    (.decl (str1 "#ccp.k"), "Sp$D$_35_ccp_46_k"),
    (.decl (str2 "#ccp" "k"), "Sp$D$_35_ccp$k"),
    (.decl (str1 "#ccp.c"), "Sp$D$_35_ccp_46_c"),
    (.decl (str2 "#ccp" "c"), "Sp$D$_35_ccp$c"),
    (.decl (str1 "SparkleMem_combo_4_8"), "Sp$D$SparkleMem__combo__4__8"),
    (.decl (str2 "SparkleMem" "combo_4_8"), "Sp$D$SparkleMem$combo__4__8"),
    (.mem true 4 8, "SparkleMem_combo_4_8"),
    (.mem false 3 5, "SparkleMem_sync_3_5"),
    (.mem true 10 128, "SparkleMem_combo_10_128"),
    (.decl (str1 "a$b"), "Sp$D$a_36_b"),
    (.decl (str1 "Sp$D"), "Sp$D$Sp_36_D"),
    (.decl (str2 "Sp" "d"), "Sp_d"),
    (.decl (str2 "α" "x"), "Sp$D$_945_$x"),
    (.decl (str1 "module"), "Sp$D$module"),
    (.decl (str1 "always_ff"), "Sp$D$always__ff"),
    (.decl (str2 "1a" "b"), "Sp$D$1a$b"),
    (.decl (str1 "foo'"), "Sp$D$foo_39_"),
    (.decl (str1 "Foo"), "Sp$D$Foo"),
    (.decl privName, "Sp$D$__private$M$_0$M$f"),
    (.aux (str3 "Tests" "Foo" "bar"), "Sp$X$Tests$Foo$bar") ]

-- Every row has the stated name.
#guard table.all fun r => encode r.1 == r.2

-- Every row is read back.
#guard table.all fun r => decode r.2 == some r.1

-- The names of the table are pairwise different.
#guard decide ((table.map fun r => r.2).Nodup)

-- The emitter's normalisation leaves every row unchanged.
#guard table.all fun r => Sparkle.Backend.Verilog.sanitizeName r.2 == r.2

-- Every row is a legal module identifier (first character, alphabet, not a
-- keyword) — tested here, NOT proved in general.
#guard table.all fun r => Sparkle.IR.ModuleNames.legal r.2

-- No keyword contains `$` (so no tagged name is a keyword).
#guard Sparkle.IR.ModuleNames.keywords.all fun k => !k.toList.contains '$'

-- A memory module's name is the text it was before the renaming.
#guard [(true, 4, 8), (false, 3, 5), (true, 0, 0), (false, 12, 1024)].all fun (p : Bool × Nat × Nat) =>
  ofMem p.1 p.2.1 p.2.2 ==
    "SparkleMem_" ++ (if p.1 then "combo" else "sync") ++ "_" ++ toString p.2.1 ++ "_" ++
      toString p.2.2

-- For a plain name the module name is what the emitter printed before:
-- `sanitizeName` of the printed declaration name.
#guard [str3 "Tests" "Foo" "bar", str1 "foo", str2 "A" "b_c", str2 "Sp" "d",
    `Tests.Compiler.CacheCoherenceProbe.nTop, `Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt].all
  fun n => isSafe n && ofDecl n == Sparkle.Backend.Verilog.sanitizeName n.toString

-- The two H pairs, by the general theorem (kernel-checked).
example : ofDecl k1Name ≠ ofDecl k2Name :=
  Tools.ShippingModuleName.ofDecl_ne (fun h => by
    have h' : Name.str Name.anonymous "#ccp.k" =
        Name.str (Name.str Name.anonymous "#ccp") "k" := h
    injection h' with h1 _
    cases h1)

example : ofDecl c1Name ≠ ofDecl c2Name :=
  Tools.ShippingModuleName.ofDecl_ne (fun h => by
    have h' : Name.str Name.anonymous "#ccp.c" =
        Name.str (Name.str Name.anonymous "#ccp") "c" := h
    injection h' with h1 _
    cases h1)

-- A declaration named like a memory module does not have its name.
example : ofDecl (Name.str Name.anonymous "SparkleMem_combo_4_8") ≠ ofMem true 4 8 :=
  Tools.ShippingModuleName.ofDecl_ne_ofMem _ _ _ _

example (k : Key) : Sparkle.Backend.Verilog.sanitizeName (encode k) = encode k :=
  Tools.ShippingModuleName.sanitizeName_encode k

/-! ## 2. The four tops of Finding H -/

def sName : Name := Name.mkStr Name.anonymous "SparkleMem_combo_4_8"
def nAName : Name := `Tests.Compiler.CacheCoherenceProbe.nA
def nBName : Name := `Tests.Compiler.CacheCoherenceProbe.nB
def mAName : Name := `Tests.Compiler.CacheCoherenceProbe.mA
def mBName : Name := `Tests.Compiler.CacheCoherenceProbe.mB
def memKidName : Name := `Tests.Compiler.CacheCoherenceProbe.memKid

/-- The modules of a design with a given name. -/
def named (d : Dsn) (s : String) : List Mod := d.modules.filter fun m => m.name == s

/-- A statement of the module mentions the constant `v` of width 8. -/
def hasConst (m : Mod) (v : Nat) : Bool :=
  m.body.any fun s => ((stmtStr s).splitOn ("Expr.const " ++ toString v ++ " 8")).length > 1

/-- One run of the real entry from reset refs: the design and the clashes of
the cache it leaves. Throws if the entry throws. -/
def runTop (top : Name) : MetaM (Dsn × Nat) := do
  let (t?, msg) ← runFull top
  let es : List (Name × (Mod × Dsn)) := (← (sparkleChildCache.get : IO _)).toList
  let cl : List String := clashes es
  resetRefs
  sparkleSynthDepth.set 0
  match t? with
  | none => throwError "MODNAMEINJ {top}: the entry threw: {msg}"
  | some t => return (designOf t, cl.length)

/-- The one module of `d` named after declaration `n`. -/
def theMod (top : Name) (d : Dsn) (n : Name) : MetaM Mod := do
  match named d (ofDecl n) with
  | [m] => return m
  | ms => throwError "MODNAMEINJ {top}: {ms.length} modules named {ofDecl n} (of {n}), expected 1"

/-- `parent` instantiates `good` (at least once) and never `bad`. -/
def callsOnly (top : Name) (d : Dsn) (parent good bad : Name) : MetaM Unit := do
  let p ← theMod top d parent
  unless instOf p (ofDecl good) ≥ 1 do
    throwError "MODNAMEINJ {top}: {parent} does not instantiate {ofDecl good}"
  unless instOf p (ofDecl bad) == 0 do
    throwError "MODNAMEINJ {top}: {parent} instantiates {ofDecl bad}, the module of {bad}"

/-- The two colliding children: two modules, two names, the `+ 1` one and the
`+ 2` one. -/
def twoKids (top : Name) (d : Dsn) (one two : Name) : MetaM Unit := do
  unless ofDecl one != ofDecl two do
    throwError "MODNAMEINJ {top}: {one} and {two} have ONE module name {ofDecl one}"
  let m1 ← theMod top d one
  let m2 ← theMod top d two
  unless m1 != m2 do throwError "MODNAMEINJ {top}: the modules of {one} and {two} are equal"
  unless hasConst m1 1 && !hasConst m1 2 do
    throwError "MODNAMEINJ {top}: the module of {one} is not the + 1 one"
  unless hasConst m2 2 && !hasConst m2 1 do
    throwError "MODNAMEINJ {top}: the module of {two} is not the + 2 one"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"MODNAMEINJ TABLE: {table.length} rows"
  -- nTop: nA calls «#ccp.k» (+ 1), nB calls «#ccp».k (+ 2)
  let (d, cl) ← runTop nTopName
  twoKids nTopName d k1Name k2Name
  callsOnly nTopName d nAName k1Name k2Name
  callsOnly nTopName d nBName k2Name k1Name
  unless cl == 0 do throwError "MODNAMEINJ {nTopName}: {cl} cache clashes"
  let names1 : List String := d.modules.map fun m => m.name
  logInfo m!"MODNAMEINJ {nTopName}: two modules {ofDecl k1Name} / {ofDecl k2Name}, nA -> the first, nB -> the second, clashes 0; modules={names1}"
  -- nDirect: the top calls both
  let (d, cl) ← runTop nDirectName
  twoKids nDirectName d k1Name k2Name
  let p ← theMod nDirectName d nDirectName
  unless instOf p (ofDecl k1Name) ≥ 1 && instOf p (ofDecl k2Name) ≥ 1 do
    throwError "MODNAMEINJ {nDirectName}: the top does not instantiate both children"
  unless cl == 0 do throwError "MODNAMEINJ {nDirectName}: {cl} cache clashes"
  let names2 : List String := d.modules.map fun m => m.name
  logInfo m!"MODNAMEINJ {nDirectName}: two modules, the top instantiates both, clashes 0; modules={names2}"
  -- mTop: mA calls «#ccp.c» (counts by 1), mB calls «#ccp».c (counts by 2)
  let (d, cl) ← runTop mTopName
  twoKids mTopName d c1Name c2Name
  callsOnly mTopName d mAName c1Name c2Name
  callsOnly mTopName d mBName c2Name c1Name
  unless cl == 0 do throwError "MODNAMEINJ {mTopName}: {cl} cache clashes"
  let names3 : List String := d.modules.map fun m => m.name
  logInfo m!"MODNAMEINJ {mTopName}: two modules {ofDecl c1Name} / {ofDecl c2Name}, mA -> the first, mB -> the second, clashes 0; modules={names3}"
  -- mmTop: a declaration named like the built memory module
  let (d, cl) ← runTop mmTopName
  let s ← theMod mmTopName d sName
  let memN : String := ofMem true 4 8
  unless ofDecl sName != memN do
    throwError "MODNAMEINJ {mmTopName}: the declaration has the memory module's name"
  let mems : List Mod := named d memN
  unless mems.all (fun m => Sparkle.Compiler.MachMemory.isMemModule true 4 8 m) do
    throwError "MODNAMEINJ {mmTopName}: a module named {memN} is not the memory module"
  unless mems.length ≤ 1 do
    throwError "MODNAMEINJ {mmTopName}: {mems.length} modules named {memN}"
  unless !(Sparkle.Compiler.MachMemory.isMemModule true 4 8 s) && hasConst s 1 do
    throwError "MODNAMEINJ {mmTopName}: the module of {sName} is not the declaration's (wd + 1)"
  let p ← theMod mmTopName d mmTopName
  unless instOf p (ofDecl sName) ≥ 1 && instOf p memN == 0 do
    throwError "MODNAMEINJ {mmTopName}: the top does not instantiate the declaration's module"
  let kid ← theMod mmTopName d memKidName
  unless instOf kid (ofDecl sName) == 0 do
    throwError "MODNAMEINJ {mmTopName}: memKid instantiates the declaration's module"
  unless mems.isEmpty || instOf kid memN ≥ 1 do
    throwError "MODNAMEINJ {mmTopName}: a memory module is in the design and memKid does not instantiate it"
  unless cl == 0 do throwError "MODNAMEINJ {mmTopName}: {cl} cache clashes"
  let names4 : List String := d.modules.map fun m => m.name
  logInfo m!"MODNAMEINJ {mmTopName}: the declaration's module {ofDecl sName} and {mems.length} memory module(s) {memN} are different modules, the top instantiates the declaration's, clashes 0; modules={names4}"

end Tests.Compiler.ModuleNameInjectiveTest
