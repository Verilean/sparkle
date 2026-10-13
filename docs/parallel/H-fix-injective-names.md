# Finding H fix: module names injective in the declaration name

Branch `fix/module-name-injective`, from `poc/roundtrip-proof` d287f2ac. Worker A.
**Nothing here was built, run or simulated.** Every Lean file is WRITTEN, NOT BUILT;
"PREDICTED" = concluded from read lines. Before this branch Finding H was measured at
the DESIGN level only (`docs/parallel/H-name-collision.md`); it was **never simulated**,
before or after — the simulation driver of this branch is written, not run.

Commits (build in this order):

| | commit | content | builds alone? |
|---|---|---|---|
| C1 | b84eede5 | `Sparkle/IR/ModuleName.lean`, `Tools/ShippingModuleName.lean` | yes (pure; nothing uses it) |
| C2 | 2fff13a5 | `Elab.lean` (4 sites), `MachMemory.lean` (1 site) | `Sparkle` yes; `Tools`/`Tests` need C3 |
| C3 | 8c718b78, 3465696a | `Tools/` (68 files), `Tests/` (20 files), 3 sim drivers | textual; see §6 |
| C4 | de17c631 | `Tests/Compiler/ModuleNameInjectiveTest.lean`, `scripts/shipping-coverage/module_name_sim.{sh,lean}` | needs C1–C3 |
| C5 | this file | | |

## 0. The ruling (user / reviewer, 2026-10-13, second message), as given to the worker

> 1. First a SMALL PURE encoding function and general lemmas (`decode (encode n) = some n`,
>    hence injectivity), THEN connect each path. Distinguish `Name.anonymous` / `.str` /
>    `.num`, component boundaries, Unicode, numeric vs string components. Identification by
>    `Name.toString` or by a hash alone is NOT acceptable.
> 2. Injectivity must survive the SV emitter's `sanitizeName`: internal `Module.name`
>    injectivity alone is not completion. Put declaration modules / generated memories /
>    auxiliary modules in SEPARATE TAGGED namespaces so that a user declaration using the
>    escape prefix or a `SparkleMem…` name cannot collide. If a compatibility fast path for
>    "safe" names is kept, PROVE its image is disjoint from the encoded image — "ordinary
>    names unchanged, special names prefixed" alone can create new collisions.
> 3. Connect consistently: `Module.name`, instance references, `design.topModule`, cache /
>    design dedup, file names / external top designation. If ordinary names must change,
>    record the scope and fix wrappers / callers together.
> 4. Turn H's `nTop` / `nDirect` / `mTop` / `mmTop` into ASSERTING regression tests (the +1
>    child and the +2 child are DIFFERENT modules, each parent instantiates the right one),
>    and compile the real writer output and compare with the source by simulation. Before the
>    renaming H was NOT simulated — keep that distinction in every record.
> 5. Name injectivity does not by itself give cache coherence: do not claim it.

## 1. The encoding (`Sparkle/IR/ModuleName.lean`, 267 lines, no `String` operation but `toList` / `ofList`)

```lean
inductive Key | decl (n : Name) | mem (combo : Bool) (aw dw : Nat) | aux (n : Name)
def encode (k : Key) : String := String.ofList (encodeL k)
def decode (s : String) : Option Key := decTop (splitOn '$' s.toList)
def ofDecl (n : Name) : String := encode (.decl n)
def ofMem (combo : Bool) (aw dw : Nat) : String := encode (.mem combo aw dw)
```

What the compiler names (READ: `CircuitM.init` is called at three places in `Elab.lean`,
all with the declaration; `MachMemory.memModule` builds the memory module; nothing else
creates a `Module.name` — `closeMachine`, the optimizer, `RegDedup`, `deinline` keep it):
a DECLARATION's module (`decl`) and a machine-route MEMORY module (`mem`). `aux` is a
reserved tagged namespace; nothing produces it. External / primitive modules
(`Module.primitive name`, `emitInstance "TSMC_SRAM_256x32"`) carry the USER's string: they
are references by SystemVerilog name, not generated names, and are not encoded (§7).

Alphabet of the image: ASCII letters, digits, `_`, `$` — exactly what `sanitizeName` keeps.

Three forms, pairwise disjoint:

* **PLAIN** (the fast path; no `$`). A declaration `N1.….Nk.last` (k ≥ 0), all components
  strings, every `Ni` non-empty, upper-case-initial (`A`–`Z`), letters and digits only, and
  not `SparkleMem`; `last` lower-case-initial (`a`–`z`), letters, digits and `_`; and the
  result not a SystemVerilog keyword (`ModuleNames.keywords`). Name: `N1_…_Nk_last` — the
  identifier the emitter printed before. Read back: split at `_`; the leading
  upper-case-initial pieces are the `Ni`; the rest, rejoined with `_`, is `last`
  (`regroup`). "Safe" = `isSafe n` = `(safeName n).isSome`; the facts are the structure
  `Tools.ShippingModuleName.Plain`.
* **MEMORY** (no `$`; first `_`-piece `SparkleMem`): `SparkleMem_{combo|sync}_{aw}_{dw}`,
  the text it had before (own decimal printer `natChars`; equality with `toString` tested,
  §5).
* **TAGGED** (always contains `$`): `Sp$D$f1$…$fk` for every other declaration, `Sp$X$…`
  for `aux`. One `$`-field per component, root first; `Name.anonymous` is `Sp$D`.
  A string component: letters and digits kept; `_` written `__`; any other character
  written `_<decimal code point>_` (so a field is `_`-pieces alternating a literal run and
  a character code; the code of `_` is empty; always an ODD number of pieces). A numeric
  component `n`: `_<decimal n>` (exactly TWO pieces — that is how `.num` and `.str` are
  told apart).

`decode` is a left inverse; it does not reject every string outside the image (not needed
for injectivity).

### Table (PREDICTED by hand from the definitions; the test `#guard`s every row)

| name | key | module name | form |
|---|---|---|---|
| `Tests.Foo.bar` | decl | `Tests_Foo_bar` | plain (as before) |
| `foo` | decl | `foo` | plain |
| `A.b_c` | decl | `A_b_c` | plain (as before) |
| `A.b.c` | decl | `Sp$D$A$b$c` | tagged (`b` is a lower-case namespace) |
| `«A_b».c` | decl | `Sp$D$A__b$c` | tagged |
| `A_b_c` (one component) | decl | `Sp$D$A__b__c` | tagged |
| `Name.anonymous` | decl | `Sp$D` | tagged |
| `«»` (one empty component) | decl | `Sp$D$` | tagged |
| `A.«1»` (string) | decl | `Sp$D$A$1` | tagged |
| `A.1` (numeric) | decl | `Sp$D$A$_1` | tagged |
| `A.«_1»` | decl | `Sp$D$A$__1` | tagged |
| `«A.b»` (one component) | decl | `Sp$D$A_46_b` | tagged |
| `A.b` | decl | `A_b` | plain |
| `«#ccp.k»` (H: `+ 1`) | decl | `Sp$D$_35_ccp_46_k` | tagged |
| `«#ccp».k` (H: `+ 2`) | decl | `Sp$D$_35_ccp$k` | tagged |
| `«#ccp.c»` / `«#ccp».c` (H: `mTop`) | decl | `Sp$D$_35_ccp_46_c` / `Sp$D$_35_ccp$c` | tagged |
| `SparkleMem_combo_4_8` (H: `mmTop`, a declaration) | decl | `Sp$D$SparkleMem__combo__4__8` | tagged |
| `SparkleMem.combo_4_8` | decl | `Sp$D$SparkleMem$combo__4__8` | tagged (`SparkleMem` is reserved) |
| memory combo 4 8 | mem | `SparkleMem_combo_4_8` | memory (as before) |
| `«a$b»`, `«Sp$D»` | decl | `Sp$D$a_36_b`, `Sp$D$Sp_36_D` | tagged (the escape character itself) |
| `Sp.d` | decl | `Sp_d` | plain (cannot imitate the tag: no `$`) |
| `«α».x` | decl | `Sp$D$_945_$x` | tagged (non-ASCII) |
| `module`, `always_ff` | decl | `Sp$D$module`, `Sp$D$always__ff` | tagged (keywords) |
| `«1a».b` | decl | `Sp$D$1a$b` | tagged (leading digit) |
| `foo'` | decl | `Sp$D$foo_39_` | tagged |
| `Foo` | decl | `Sp$D$Foo` | tagged (upper-case-initial last component) |
| `_private.M.0.M.f` | decl | `Sp$D$__private$M$_0$M$f` | tagged |
| `Tests.Foo.bar` | aux | `Sp$X$Tests$Foo$bar` | tagged |

`sanitizeName` handles neither leading digits nor keywords (its own doc); the encoding
does: such names are tagged, and a tagged name starts with `S` and contains `$`.

### Fast path: KEPT. Why, and what it costs

Without a fast path every emitted module identifier changes: every wrapper that
instantiates a generated top by name (FPGA flows, `#sim`'s Verilator top, hand-written
testbenches), every pinned text, every digest. With it, the identifier of a plain name is
unchanged. Measured by grep on d287f2ac (not by a build):

* 391 distinct declarations are arguments of a synthesis command in the repo; ALL 391 have
  a lower-case-initial last component of letters, digits, `_` (221 contain `_`);
* 800 distinct namespace components in `Tests/ Examples/ IP/ Sparkle/`; all but 3 are
  upper-case-initial alphanumeric (`BLS12_381`, `a`, `cooperative_groups`);
* 136 `@[hardware_module]` declarations; the 5 that are not plain by their last component
  are the probe's own (`«#ccp…»`, `SparkleMem_combo_4_8`).

So the plain form covers the corpus except declarations under a namespace like
`BLS12_381` (they become tagged: their emitted identifier CHANGES — NOT swept which
synthesized declarations live there), primed names (`foo'`: before `foo_prime`, now
`Sp$D$…foo_39_`), private declarations, and upper-case-initial definitions.

A simpler safe set ("no `_` in any component") would have renamed 221 of the 391. The
price of the larger set is the read-back rule (`regroup`) and five more lemmas; the
disjointness and the injectivity of the fast path are PROVED (§2), not argued.

What changes even for a plain name: `Module.name` itself, from the dotted `A.B.c` to
`A_B_c` (the ruling's point 2 is met by making `sanitizeName` the IDENTITY on names, which
a dotted name cannot give). Emitted consequence: the comment line `// Module: A.B.c`
becomes `// Module: A_B_c`. Nothing else of the text of a plain-named design changes
(PREDICTED: instance-name hints `inst_<name>` were normalised `.`→`_` before and are the
same string now; `inst{k}_<name>` of the machine route was sanitised at emission).

## 2. The lemmas (`Tools/ShippingModuleName.lean`, 926 lines, 86 theorems; imports only the encoding and `Sparkle.Backend.Verilog`)

Verbatim:

```lean
theorem decode_encode (k : Key) : decode (encode k) = some k
theorem encode_injective {a b : Key} (h : encode a = encode b) : a = b
theorem ofDecl_injective {a b : Name} (h : ofDecl a = ofDecl b) : a = b
theorem ofDecl_ne {a b : Name} (h : a ≠ b) : ofDecl a ≠ ofDecl b
theorem ofMem_injective {c c' : Bool} {a d a' d' : Nat} (h : ofMem c a d = ofMem c' a' d') :
    c = c' ∧ a = a' ∧ d = d'
theorem ofDecl_ne_ofMem (n : Name) (c : Bool) (a d : Nat) : ofDecl n ≠ ofMem c a d
theorem ofDecl_ne_aux (n n' : Name) : ofDecl n ≠ encode (Key.aux n')
theorem ofMem_ne_aux (c : Bool) (a d : Nat) (n : Name) : ofMem c a d ≠ encode (Key.aux n)

-- the fast path
structure Plain (ns : List (List Char)) (last : List Char) : Prop where
  upper : ∀ s, s ∈ ns → startsUpper s = true
  alnum : ∀ s, s ∈ ns → ∀ (x : Char), x ∈ s → x.isAlphanum = true
  notMem : ∀ s, s ∈ ns → s ≠ memHead
  lower : startsLower last = true
  lastChars : ∀ (x : Char), x ∈ last → x.isAlphanum = true ∨ x = '_'
theorem safeName_spec {n : Name} {ns : List (List Char)} {last : List Char}
    (h : safeName n = some (ns, last)) :
    compsRev n = (last :: ns.reverse).map Comp.str ∧ Plain ns last
theorem plain_no_dollar {ns : List (List Char)} {last : List Char} (hp : Plain ns last) :
    '$' ∉ plainL ns last
theorem tagged_has_dollar (k : Char) (cs : List Comp) : '$' ∈ tagged k cs
theorem safe_no_dollar {n : Name} (h : isSafe n = true) : '$' ∉ encodeL (Key.decl n)
theorem unsafe_has_dollar {n : Name} (h : isSafe n = false) : '$' ∈ encodeL (Key.decl n)
theorem safe_ne_unsafe {a b : Name} (ha : isSafe a = true) (hb : isSafe b = false) :
    ofDecl a ≠ ofDecl b
theorem safe_injective {a b : Name} (_ha : isSafe a = true) (_hb : isSafe b = true)
    (h : ofDecl a = ofDecl b) : a = b

-- the emitter
theorem encode_clean (k : Key) : Sparkle.IR.NameHints.Clean (encode k)
theorem sanitizeName_encode (k : Key) :
    Sparkle.Backend.Verilog.sanitizeName (encode k) = encode k
theorem sanitized_injective {a b : Key}
    (h : Sparkle.Backend.Verilog.sanitizeName (encode a) =
      Sparkle.Backend.Verilog.sanitizeName (encode b)) : a = b
```

How: everything on `List Char`. `split_join` (`splitOn d (join d segs) = segs` when no
segment contains `d`), `split_join_last` (the last segment may contain `d`), `join_split`;
decimal `undigs_digsF` (fuel, no well-founded recursion — the functions evaluate);
`unpieces_pieces`, `decComp_enc`, `decAll_enc`; `nameOfRev_compsRev`; the three forms
`decTop_plain`, `decTop_mem`, `decTop_tagged_D` / `_X`. Injectivity is ONE statement
(`encode_injective`, from `decode_encode`); disjointness across tags and across the fast
path are its instances, and the `$` statements say the same by characters. The fast path's
injectivity on safe names includes `.num` and `«»` names vacuously: they are not safe.

NOT proved: (i) `ModuleNames.legal (encode k) = true` (first character, not a keyword) —
`#guard`ed on the table, and "no keyword contains `$`" is `#guard`ed; (ii) for a safe `n`,
`ofDecl n = sanitizeName n.toString` (the old emitted identifier) — `Name.toString` does
not evaluate in the kernel (`Tools/ShippingNameSep.lean`, header); `#guard`ed on six names;
(iii) `ofMem c a d` is the old `s!"SparkleMem_…"` — `#guard`ed on four parameter triples.

## 3. Sites (C2). Before → after

| file:line (after) | before | after |
|---|---|---|
| `Sparkle/Compiler/Elab.lean` 2941 (`synthesizeCertified`) | `CircuitM.init declName.toString` | `CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName)` |
| 2966 (`synthesizeMixedCertified`) | same | same |
| 5358 (`synthesizeFromConst`, legacy arm) | same | same |
| 9318 (`#sim`: top lookup) | `let topModName := toString declName` | `… := Sparkle.IR.ModuleName.ofDecl declName` |
| `Sparkle/Compiler/MachMemory.lean` 51 (`memModule`) | `s!"SparkleMem_{…}_{aw}_{dw}"` | `Sparkle.IR.ModuleName.ofMem combo aw dw` |

Every other use takes the name FROM a module and follows (READ, not changed):

* `Module.name`, `Design.topModule`: `CircuitM.init` (`Sparkle/IR/Builder.lean` 59–64) sets both;
* instance references: `emitInstance subModule.name …` (`Elab.lean` 6735, 6751, 8595, 8657),
  `.inst mc.name …` (`Sparkle/IR/Machine.lean` 286, `MachineInstG.lean` 49);
* instance NAMES: `inst_{subModule.name}` (fresh-name hint), `inst{k}_{mc.name}`;
* design dedup / join by name: `Elab.lean` 5553, 6581, 7990, 8532, 9060, 9065,
  `designWith` (`Machine.lean` 302–305), `moduleByName`;
* the child cache: keyed by the declaration `Name` (unchanged);
* the writer: `designArtifact` compares `m.name == d.topModule` (`VerilogDesign.lean` 27);
  `emitModule` prints `sanitizeName m.name` (`Verilog.lean` 452) and the instance target
  `sanitizeName moduleName` (395) — both the identity on encoded names
  (`sanitizeName_encode`), so definition and reference stay equal and injective;
* `ModuleNameCheck.check` / `checkDesign` (`finishSynth`, `validateDesignNames`): now always
  pass for compiler-made names (PREDICTED; legality is tested, not proved). The success
  domain GROWS: names that were rejected (a keyword, a leading digit, non-ASCII, two names
  that normalised alike such as `A.b_c` / `A.b.c`) are accepted. No source is newly rejected.
* C backend: `sanitizeName m.name` (`CSim.lean` 1599, 1843, 2117, 2553, 2643) — its own
  `sanitizeName` keeps `$` too; a TAGGED name therefore puts `$` into a C identifier
  (accepted by gcc / clang as an extension; NOT checked for the JIT compiler in use).

File names / external top designation: the `#write…` commands take the path from the user;
`#sim` / `#simChecked` name their files by the LAST component of the declaration
(`Elab.lean` 9303, `SimChecked.lean` 82) — that is not injective (two declarations `A.f`,
`B.f` share `.lake/build/gen/sim/f.sv`), it was so before, and it is NOT changed here
(the JIT artifacts are keyed by it). Recorded as open.

## 4. Statement changes forced in `Tools/` (C3)

Rule applied: wherever a printed declaration name stood for a MODULE name, it is now
`Sparkle.IR.ModuleName.ofDecl`. Textual, by script; counts are substitutions.

* `declName.toString` ↦ `(Sparkle.IR.ModuleName.ofDecl declName)`: 559 in 49 files (228 in
  `ShippingRegisterSoundness`, 102 in `ShippingInstanceEntrySoundness`, 32 in
  `ShippingMemoryEntrySoundness`, 24 in `ShippingHarnessSpine`, …). These are the mirrors of
  the compiler's `CircuitM.init declName.toString` and statements such as
  `m.name = declName.toString`; the proofs treat the string as an opaque parameter.
* callee forms, 126 in 23 files: `c.toString`, `c'.toString`, `c.1.toString`,
  `(d.shape.insts[k]).1.toString`, `(calleeAt d k).toString`, `fun n => n.toString`, and the
  generators' quoted `($cq : Lean.Name).toString`.

The structure fields and premises that change (each `X.toString` ↦ `ofDecl X`):

| statement | file |
|---|---|
| `ChildIface….name : b.name = c.toString` | `ShippingSeqChildIface` 42, `ShippingCallsKidsD` 39, `ShippingKidsChildIface` 86 |
| `….name : m.name = c.toString` | `ShippingGatePorts` 203 |
| `M.name = c.toString` (in conjunctions) | `ShippingChecksCore` 89, 466; `ShippingSeqChildIface` 161; `ShippingLeafOneOut` 758; `ShippingMachineChildRun` 55; `ShippingCallsGate` 227 |
| `hself : c.toString ∉ namesOf d namesK`, `self : …` | `ShippingChecksRun` 207, `ShippingChecksRun2` 62, 167, `ShippingChecksCore` 309, 382, `ShippingKidsChildIface` 150, 378, `ShippingOneOutKid` 218, `ShippingGenKid` 259, `ShippingMemClosesKids` 175 |
| `hnames : … c.toString = c'.toString → c = c'`, `hparent : … c.1.toString ≠ declName.toString`, `hfresh : … o.name ≠ s!"inst{gi}_{c.1.toString}"`, `hselfD`, `hdisjD` | `ShippingCallsKidsS` (3 theorems), `ShippingCallsKidsD`, `ShippingCallsSeqKids`, `ShippingCallsGate`, `ShippingMemClosesKids`, and the generators `ShippingMachineClosesAtGen(G)`, `ShippingChildIfaceGen`, `ShippingCallsKidsSGen`, `ShippingNoPorts{Kids,Deep,Mem,MemSeq}Command` |
| `namesK` / `declsOf` lists: `….map fun n => n.toString` | `ShippingKidsChildIface` 118–119 and the generators |

`Tools/ShippingNameSep.lean`: the existing theorems (about `Name.toString`: `toString_mem`,
`toString_ne`, `sepFast_ne`, `sep_ne`, the `…_of` families) are UNTOUCHED. A namespace
`Tools.ShippingNameSep.Enc` is appended with the same names, arguments and Boolean checks
and `ofDecl` conclusions:

```lean
theorem Enc.sep_ne {a b : Lean.Name} (h : sep a b = true) : ofDecl a ≠ ofDecl b
theorem Enc.hparent_of {α : Type} (insts : List (Lean.Name × α)) (parent : Lean.Name)
    (h : (insts.all fun c => sep c.1 parent) = true) : ∀ c ∈ insts, ofDecl c.1 ≠ ofDecl parent
theorem Enc.hnames_of (L : List Lean.Name) (_h : …) :
    ∀ c ∈ L, ∀ c' ∈ L, ofDecl c = ofDecl c' → c = c'
theorem Enc.not_mem_map_of (c : Lean.Name) (L : List Lean.Name)
    (h : (L.all fun c' => sep c c') = true) : ofDecl c ∉ L.map (fun n => ofDecl n)
theorem Enc.disjoint_map_of …   theorem Enc.nodup_map_of …   -- and the B / ' forms
theorem Enc.not_mem_of (c : Lean.Name) (names : List String)
    (h : decide (ofDecl c ∉ names) = true) : ofDecl c ∉ names
theorem Enc.fresh_of (c : Lean.Name) (f : String → String) (o : String)
    (h : decide (o ≠ f (ofDecl c)) = true) : o ≠ f (ofDecl c)
theorem Enc.not_mem_nil (c : Lean.Name) : ofDecl c ∉ ([] : List String)
theorem Enc.not_mem_cons_mem (c : Lean.Name) (cb : Bool) (aw dw : Nat) (rest : List String)
    (h : ofDecl c ∉ rest) : ofDecl c ∉ ofMem cb aw dw :: rest
```

The checks are kept so that no generator's test or `(by decide)` changes; they are used
only to get `a ≠ b` (`hnames_of` does not need its check at all any more). This is NOT a
weakening of an endpoint: the premises have the same shape about the new name function,
and they are discharged by the same decided checks. What it does NOT yet do is REMOVE the
name premises from the endpoints, which injectivity now allows (`ofDecl a ≠ ofDecl b` from
`a ≠ b`, decidable on `Name`s without printing) — a follow-up, not done.

`not_mem_of` / `fresh_of` (a name against an ARBITRARY string) cannot use the candidate
renderings; they take the decided statement, which EVALUATES `ofDecl c` in the kernel. For
the lists the generators pass — names of memory modules — the tactic `name_not_mem` first
tries `not_mem_nil` / `not_mem_cons_mem` (no evaluation). Twelve call sites use it (3 in the
generators, 9 in tests).

`Tests/` (20 files): the same substitutions in statements; the two pinned names of
`ShippingHierarchySoundnessTest` (`"Sparkle.Tests….childAdd"` ↦ `"Sparkle_Tests_…_childAdd"`,
`childTwo`); five run-time lookups `m.name == toString n` ↦ `ofDecl n`; and — so that no
audit is silently weakened — the audits that scan a statement for the constant
`Lean.Name.toString` (`OneOutTwoCalleeTest`, `ShippingCallsCloseTest`,
`ShippingChildBoundaryTest`) now scan for `Lean.Name.toString` OR
`Sparkle.IR.ModuleName.ofDecl`, and their `getUsedConstants.contains` look for
`Tools.ShippingNameSep.Enc.hparent_of` / `Enc.hnames_of`.

## 5. Tests (C4)

`Tests/Compiler/ModuleNameInjectiveTest.lean` (imports the probe; target-only until the
integrator adds it to `Tests/AllTests.lean`): THROWS on failure.

* the table of §1 (34 rows): `encode` gives the stated name; `decode` reads it back; the
  names are pairwise different; `sanitizeName` leaves each unchanged; each is
  `ModuleNames.legal`; no keyword contains `$`; `ofMem` = the old text on four triples;
  `ofDecl n = sanitizeName n.toString` and `isSafe n` on six plain names. `#guard`s:
  evaluated by the compiler, not the kernel. Three `example`s apply the general theorems to
  the H pairs (kernel-checked).
* `nTop`, `nDirect`, `mTop`, `mmTop`: from reset refs, the real entry; the design holds
  exactly one module named `ofDecl` of each colliding declaration, the two names differ, the
  two modules differ, the first holds the constant 1 and not 2, the second 2 and not 1;
  `nA`/`mA` instantiate the first and never the second, `nB`/`mB` the reverse; `nDirect`'s
  top instantiates both; for `mmTop` the declaration's module (`wd + 1`) is not the memory
  module, every module named `SparkleMem_combo_4_8` is `isMemModule true 4 8`, the top
  instantiates the declaration's module; and the probe's `clashes` of the cache the run
  leaves is 0. Line: `MODNAMEINJ <top>: …`.

`scripts/shipping-coverage/module_name_sim.{sh,lean}` (the pattern of `nested_let_sim.*`):
the text of the real `#writeVerilogDesign` for the four tops, compiled with a testbench
and compared with the Lean source cycle by cycle:

    MODNAMESIM <decl>: command==source <T/F/-> x-cycles=<n> cycles=<n>

PREDICTED on this branch: `T`, `x-cycles=0` for `nTop`, `nDirect`, `mTop`. For `mmTop`: `T`
IF the testbench's zeroing of the memory is accepted by the simulator (the emitted memory
has no initial contents; the source's starts at zero; the testbench assigns zero to every
memory of the hierarchy after each reset phase) and if the source's memory indeed starts at
zero — otherwise `F` with x cycles or `-`; that would say nothing about names. The driver
uses no declaration of the fix, so it can be run on d287f2ac too. PREDICTED there (never
run): the text of `nTop` / `nDirect` / `mTop` is LEGAL SystemVerilog (one module `ccp_k` /
`ccp_c` — `sanitizeName` drops `#` — instantiated by both parents) and simulates WRONG
(`nB` adds 1 where the source adds 2): `command==source F`. For `mmTop` the single module
named `SparkleMem_combo_4_8` has the ports of whichever came first, the other parent's
instance names ports it does not have: PREDICTED not to elaborate (`-`).

## 6. What the integrator must run, and what is expected to change

`lakefile.lean` (not edited here):

    lean_lib «Tools.ShippingModuleName» where
      roots := #[`Tools.ShippingModuleName]

Order:

1. **C1 alone**: `Sparkle.IR.ModuleName`, `Tools.ShippingModuleName`. Independent of
   everything; fix it first. Axioms: standard (no `sorry`, no `native_decide`, no axiom).
2. **C2**: `lake build Sparkle`. Then, BEFORE Tools, on the built compiler: the corpus
   measurement with `compare_outputs.py` against d287f2ac. EXPECTED difference for a
   plain-named design: exactly the `// Module:` comment lines of modules whose declaration
   has ≥ 2 components. Any other difference is a finding (in particular an instance name).
   EXPECTED for a non-plain name: the module identifier and everything derived from it.
3. **C3**: `Tools.ShippingNameSep`, then the Tools libraries, then `Tests.AllTests`.
   EXPECTED to need hand work (risk list §8).
4. **C4**: `Tests.Compiler.CacheCoherenceProbe` (its `CACHECOH` lines now PREDICTED
   `COHERENT=T` for the four tops; it is log-only), `Tests.Compiler.ModuleNameInjectiveTest`.
5. Simulations (each under `cgrun.sh`, never next to a build): `writer_sim.sh`,
   `nested_let_sim.sh`, `optprint_sim.sh` (and `subinst_key_sim.sh`) — EXPECTED unchanged
   results (their drivers look the top up by `ofDecl` now); `module_name_sim.sh` — new.
6. Digests: every digest of EMITTED TEXT of a design with a multi-component declaration
   name is EXPECTED to change (the comment line); digests over IR `Module`s change too
   (`Module.name`). Digests of functions / traces must not change. The target-only Keccak
   tests: their emitted identifiers are plain (PREDICTED unchanged); their text digests
   change by the comment line only.

## 7. What remains open

* **Ruling point 5 — cache coherence is NOT claimed.** Injective names remove H2 of
  `docs/parallel/A-cache-coherence.md` §3 (b) (two declarations, one name) as a
  counterexample; they do not give H1 (provenance of every module of a result), H3 (no
  overwrite), nor the run-level preservation. `Coherent` is still not an invariant that is
  proved; the test measures 0 clashes in four runs.
* The endpoints still CARRY their name premises (now about `ofDecl`); removing them by
  `ofDecl_ne` is a follow-up.
* Legality of the image (`ModuleNames.legal`) and "plain = the old identifier" are tested,
  not proved (§2).
* External / primitive module names are user strings in no tagged namespace: a primitive
  the user names `Foo_bar` and a declaration `Foo.bar` are the same SystemVerilog name.
  That is linkage by the user's own string (`emitInstance`), not a generated name; the
  encoding does not address it and nothing is claimed.
* `MachMemory.memChildName` (the placeholder `Name` `SparkleMem.combo.4.8` in a shape) is a
  `Lean.Name` a user cannot declare by syntax; a declaration created with that name through
  the API would be read as a memory by `memChild?`. Not a module-name question; not touched.
* `#sim` file names by last component (§3).
* `Sparkle/IR/ModuleNames.lean`'s header still says invalid names are "not renamed by a
  new encoding" — stale after this branch; not edited (the file's content is unchanged).
* Tools/Tests prose that still says "prints" / "candidate renderings" for module names.

## 8. UNVERIFIED, in risk order

1. **C3 is a textual substitution over ~800 places, unbuilt.** It is right wherever the
   printed name is an opaque string (the bulk). It can be wrong where a proof used a
   PROPERTY of the old string: a `decide` / `rfl` on a concrete module name, a `simp` lemma
   about `toString` / string append, the memory name as an `s!` term
   (`Tools.ShippingMemCloses.isMemModule_memModule` "a simp"; `memNameAt_eq`;
   `ShippingMemOnlyCloses` name facts), `ShippingInstanceEntrySoundness`'s
   `toString "inst_" ++ toString mc.name` rewrites (unchanged text, should still match).
   Not all `Tests/` uses were found by pattern: a test that compares a module name with a
   printed name under another spelling will fail at run time ("no module named …").
2. **`name_not_mem` / `Enc.not_mem_of`**: the structural branch needs the unifier to see
   `(memModule cb aw dw).1.name` (or a test's `memName` constant) as `ofMem ?cb ?aw ?dw`;
   the fallback decides `ofDecl c ∉ names` in the kernel (`String.toList` on literals, a
   250-keyword membership, string equality) — cost and feasibility NOT measured. If both
   fail: state the lists as `ofMem …` terms and use `not_mem_cons_mem` directly.
3. **C1 proofs** (926 lines blind). Likeliest breaks: `show` goals that rely on unfolding
   structural recursion (`splitOn`, `join`, `pieces`, `regroup`); `cases h` on equations
   whose sides need `whnf`; the `by decide` on character facts (`digit_val`,
   `digit_alnum`, `memHead_alnum`, `kindOf_memKind`); `simp only […, Bool.and_eq_true,
   decide_eq_true_eq]` in `nsOk_spec` / `lastOk_spec` / `safeOk_spec`; `rw [h]` under a
   `match` in `encDeclL_safe`; `all_goals rfl` after a `rw` that already closed the goal is
   a no-op by design. `deriving DecidableEq` for `Key` (a `Name` field).
4. The generators: the quoted `Sparkle.IR.ModuleName.ofDecl` forms, and whether every
   generated statement and the theorem it is fed to changed together (a premise built by a
   generator and consumed by a hand-written theorem under a spelling the script missed).
5. `ModuleNameInjectiveTest`: the `hasConst` test reads `stmtStr` text (`Expr.const 1 8`,
   as the probe's log prints it); `mmTop` if `memKid` does not take the machine route (the
   assertions allow zero memory modules); `injection` on `Name.str` equations.
6. `module_name_sim`: the memory zeroing (an `initial`-block assignment to an array that an
   `always_ff` writes — a simulator may refuse); the source's initial memory contents; port
   order = argument order (as the existing drivers assume).
7. Tools that read `$` in identifiers: Icarus and Verilator accept it; yosys / vendor flows
   and the C JIT were not checked. Only tagged (non-plain) names contain `$`.
8. The corpus claim "all 391 command arguments are plain" is by grep of the last component
   and of `namespace` lines, not by evaluating `isSafe` on the resolved names.
