import Tests.Ved.U1EqLutCheck
import IP.Crypto.SHA256
import IP.Crypto.SHA512HW
import IP.Crypto.AESHW

/-!
# `#ved_u1` on the real constant-table leaves

The ORIGINAL declarations (no copies):

* `Sparkle.IP.Crypto.SHA256.kMux`   — 64 × 32-bit constants over a 7-bit index,
* `Sparkle.IP.Crypto.SHA512HW.kMux` — 80 × 64-bit constants over a 7-bit index,
* `Sparkle.IP.Crypto.AESHW.sboxHW`  — 256 × 8-bit constants over an 8-bit index
  (8-bit entries and 8-bit index constants: the compiler shares equal constants, so the body has
  aliases and mux operands naming the root wire).

After `#ved_u1` the facts are checked independently of the entry: the stored type of
`<decl>.ved_u1` is, as an `Expr` compared with `==`, the hand-rebuilt
`U1Stmt <decl>.ved_contract <decl>.ved_mod (@<decl> defaultDomain)`, its axioms are within
`propext`, `Classical.choice`, `Quot.sound`, and the proof went through the table route
(`<decl>.ved_tbl` holds the `TblData` the kernel checked, with the table's size).

The route (Tools/VedU1TableGen.lean): the flat `simp` over the mux chain does not scale past about
32 entries, so the table is NOT unfolded.  The kernel checks (1) the synthesized body IS the
position-indexed body of the table read from it, (2) a small Bool over the table data, and the
general lemmas evaluate such a body (`step_table`), prove it a well-ordered netlist
(`orderOk_table`) with distinct wires (`nodup_table`) once, by induction.  The declaration's own
`kLut!` chain is compared with `lutBV` of the same table by `rfl`.

Controls: a table constant of the module changed (and two swapped) is refused at `[proof]` and
leaves no `ved_*` constant.
-/

namespace Tests.Ved.U1KTabCheck

open Lean Elab Command Term Meta
open Tools.VedU1Contract Tools.VedU1Entry Tests.Ved.U1EqLutCheck

#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Crypto.SHA256.kMux
#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Crypto.SHA512HW.kMux
#guard_msgs (drop info) in
#ved_u1 Sparkle.IP.Crypto.AESHW.sboxHW

/-- independent of the entry: exact type, std3, and the table route with its entry count -/
def checkTab (decl : Name) (entries : Nat) : CommandElabM Unit := liftTermElabM do
  let nm := Names.ofBase decl
  let thm := decl ++ `ved_u1
  let stmt := mkApp (Lean.mkConst decl) (Lean.mkConst ``Sparkle.Core.Domain.defaultDomain)
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m (@{decl} defaultDomain)"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do throwError "{thm}: axioms {ax}"
  -- the table route: the registered data is accepted by the checker and has the expected size
  let some (.defnInfo di) := (← getEnv).find? (decl ++ `ved_tbl) | throwError "{decl}: no table data (not the table route)"
  let some D ← (unsafe Meta.evalExpr (Option Tools.VedU1TableGen.TblData) (mkApp (Lean.mkConst ``Option [Level.zero]) (Lean.mkConst ``Tools.VedU1TableGen.TblData))
      (mkApp2 (Lean.mkConst ``Option.some [Level.zero]) (Lean.mkConst ``Tools.VedU1TableGen.TblData) di.value) : MetaM _)
    | throwError "{decl}: table data not evaluable"
  unless D.ok = true && D.t + 1 == entries && D.tbl.length == D.t do
    throwError "{decl}: table data t={D.t}, expected {entries} entries"
  logInfo m!"OK {decl}: exact type, axioms {ax.size}, table route, {entries} entries"

/-- info: OK Sparkle.IP.Crypto.SHA256.kMux: exact type, axioms 3, table route, 64 entries -/
#guard_msgs in
run_cmd checkTab ``Sparkle.IP.Crypto.SHA256.kMux 64
/-- info: OK Sparkle.IP.Crypto.SHA512HW.kMux: exact type, axioms 3, table route, 80 entries -/
#guard_msgs in
run_cmd checkTab ``Sparkle.IP.Crypto.SHA512HW.kMux 80
/-- info: OK Sparkle.IP.Crypto.AESHW.sboxHW: exact type, axioms 3, table route, 256 entries -/
#guard_msgs in
run_cmd checkTab ``Sparkle.IP.Crypto.AESHW.sboxHW 256

/-! ## Controls: a changed table constant is refused at `[proof]`, no `ved_*` left -/

-- SHA-256 K[5] (0x59f111f1) changed
/-- info: refused [proof], clean -/
#guard_msgs in
set_option maxRecDepth 100000 in
run_cmd ctlMut `ctlSha256Entry ``Sparkle.IP.Crypto.SHA256.kMux (bumpConst 32 5) <|
    [(17, "_tmp_mux_then_17 := const 1508970993:32", "_tmp_mux_then_17 := const 1508970994:32")]

-- SHA-256 K[1] and K[2] exchanged
/-- info: refused [proof], clean -/
#guard_msgs in
set_option maxRecDepth 100000 in
run_cmd ctlMut `ctlSha256Swap ``Sparkle.IP.Crypto.SHA256.kMux (swapConsts 32 1 2) <|
    [(5, "_tmp_mux_then_5 := const 1899447441:32", "_tmp_mux_then_5 := const 3049323471:32"),
     (8, "_tmp_mux_then_8 := const 3049323471:32", "_tmp_mux_then_8 := const 1899447441:32")]

-- the S-box entry S[1] (0x7c) changed
/-- info: refused [proof], clean -/
#guard_msgs in
set_option maxRecDepth 100000 in
run_cmd ctlMut `ctlSboxEntry ``Sparkle.IP.Crypto.AESHW.sboxHW (bumpConst 8 3) <|
    [(5, "_tmp_mux_then_5 := const 124:8", "_tmp_mux_then_5 := const 125:8")]

-- the module of SHA-256's table against SHA-512's statement
/-- info: refused [proof], clean -/
#guard_msgs in
set_option maxRecDepth 100000 in
run_cmd do ctl `ctlTabOther ``Sparkle.IP.Crypto.SHA512HW.kMux (← liftTermElabM (modOf ``Sparkle.IP.Crypto.SHA256.kMux))

end Tests.Ved.U1KTabCheck
