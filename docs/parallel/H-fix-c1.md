# Finding H fix, step C1: the pure module-name encoding and its lemmas (2026-10-13)

Tree `792459f7380eeb961a922c9ce12aaaa385d169db` = poc d0c225ff + `Sparkle/IR/ModuleName.lean` and `Tools/ShippingModuleName.lean` from
`fix/module-name-injective` b84eede5 + one `lean_lib`. NOTHING in the compiler uses the encoding yet: this
commit changes no emitted name and fixes nothing by itself. Finding H is still present on this tree.
Integrator change: one lemma (`decTop_mem`) — the `else _` placeholder of a `show` spelled out (the first
build failed there; no statement changed). cgrun 3 GiB, swap 0.

| run | command | result |
|---|---|---|
| `20261013-164504-h-c1` | `lake build Sparkle.IR.ModuleName Tools.ShippingModuleName ` | result=exit-code, memory_peak_file=730193920 |
| `20261013-164556-h-c1b` | `lake build Sparkle.IR.ModuleName Tools.ShippingModuleName ` | result=success, memory_peak_file=226689024 |
| `20261013-164608-h-c1-ax` | `lake env lean /tmp/nix-shell-91634-641856963/claude-1000/-home-junji-hashimoto-git-sparkle/0fec7b77-7ced-4e26-9969-d28bd` | result=success, memory_peak_file=2097152 |

Encoding (structural recursion on `Lean.Name`; no `Name.toString`, no hash): keys `decl n` / `mem combo aw dw`
/ `aux n`. A "plain" declaration name (upper-case-initial alphanumeric namespace components other than
`SparkleMem`, a lower-case-initial last component over letters / digits / `_`, not a keyword) is written
`N1_…_Nk_last` as today; a memory `SparkleMem_{combo|sync}_{aw}_{dw}` as today; every other declaration
name is TAGGED `Sp$D$f1$…$fk` (one field per component; `_` ↦ `__`, any other non-alphanumeric ↦
`_<codepoint>_`, a numeric component `_<n>`), which always contains `$`.

Proved (standard axioms: propext, Classical.choice, Quot.sound — `#print axioms` in run h-c1-ax):
```
theorem decode_encode (k : Key) : decode (encode k) = some k := by
  show decTop (splitOn '$' (String.ofList (encodeL k)).toList) = some k
  rw [String.toList_ofList]
  exact decTop_encodeL k

/-- **The encoding is injective**: across the tags, and within each. -/
theorem encode_injective {a b : Key} (h : encode a = encode b) : a = b := by
theorem encode_injective {a b : Key} (h : encode a = encode b) : a = b := by
  have h1 : decode (encode a) = decode (encode b) := congrArg decode h
  rw [decode_encode, decode_encode] at h1
  exact Option.some.inj h1

/-- Two declarations have one module name only if they are one declaration
(any `Lean.Name`: anonymous, numeric components, any character). -/
theorem ofDecl_injective {a b : Name} (h : ofDecl a = ofDecl b) : a = b :=
theorem ofDecl_injective {a b : Name} (h : ofDecl a = ofDecl b) : a = b :=
  Key.decl.inj (encode_injective h)
  Key.decl.inj (encode_injective h)


theorem ofDecl_ne {a b : Name} (h : a ≠ b) : ofDecl a ≠ ofDecl b :=
theorem ofDecl_ne {a b : Name} (h : a ≠ b) : ofDecl a ≠ ofDecl b :=
  fun e => h (ofDecl_injective e)

theorem ofMem_injective {c c' : Bool} {a d a' d' : Nat} (h : ofMem c a d = ofMem c' a' d') :
    c = c' ∧ a = a' ∧ d = d' :=
  Key.mem.inj (encode_injective h)

/-- No declaration — whatever its name, `SparkleMem_combo_4_8` included —
has the name of a memory module. -/
theorem ofDecl_ne_ofMem (n : Name) (c : Bool) (a d : Nat) : ofDecl n ≠ ofMem c a d := by
theorem ofDecl_ne_ofMem (n : Name) (c : Bool) (a d : Nat) : ofDecl n ≠ ofMem c a d := by
  intro e
  have h : Key.decl n = Key.mem c a d := encode_injective e
theorem safe_ne_unsafe {a b : Name} (ha : isSafe a = true) (hb : isSafe b = false) :
    ofDecl a ≠ ofDecl b := by
theorem safe_injective {a b : Name} (_ha : isSafe a = true) (_hb : isSafe b = true)
    (h : ofDecl a = ofDecl b) : a = b :=
theorem sanitizeName_encode (k : Key) :
    Sparkle.Backend.Verilog.sanitizeName (encode k) = encode k := by
theorem sanitized_injective {a b : Key}
    (h : Sparkle.Backend.Verilog.sanitizeName (encode a) =
      Sparkle.Backend.Verilog.sanitizeName (encode b)) : a = b := by
```
So: decoding inverts encoding; the three tagged namespaces do not collide; the fast path for plain names is
injective on plain names and its image is disjoint from the tagged image; `sanitizeName` is the identity on
the image, hence injectivity survives the SV emitter's sanitising.

Not proved (only `#guard`ed in the compiler file): that every image is a legal SystemVerilog identifier;
that a plain name's image equals the identifier emitted today. Not checked: `$` in identifiers under
yosys / the C JIT (tagged names only).

Next (unbuilt, on the branch): C2 the five compiler sites, C3 the forced statement changes in `Tools/`
(`declName.toString` ↦ `ofDecl declName`: 559 places in 49 files), C4 the asserting regression test and the
simulation, C5 the note.
