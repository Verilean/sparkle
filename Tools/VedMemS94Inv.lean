import Lean
import Sparkle.Core.Signal

/-!
# The register pairing of the invariant `R` (s94y, option `ved.mem.s94PairFix`)

`Tools.VedMemEntry.buildR` builds the invariant `R ins s st mems` of the memory loop: one equation `st name = (component of the loop state).toNat`
per loop-state component.  When the loops have more components than the module has registers, `Tools.VedMemShape.matchRegsShared` lets a
component SHARE a register (the synthesizer builds one register for hardware it finds equal).  Its rule (2) takes "a register already taken, of
its width, the most recent first": a guess.  On R033 the constant register `Signal.register 0#2 (Signal.pure 0#2)` of `h264FrameEncoder`
(component 19 of the last loop) shares the IR register `_tmp_a_143` of the same constant register of an earlier loop, but the guess pairs it with
`_tmp_a_786` (= `nCTblSel`, taken by component 16 just before): `R` then says `nCTblSel = 0` at every cycle, an equation that is not a theorem of
the design (hstep goal 63 of the tail: `nCTblSelNext % 4 = 0`).

`repairShared`: a component whose register is also taken by an EARLIER component (a share of the old pairing) and whose own `Signal.register init x`
is closed (it does not mention the loop's state) is paired with the register of the earliest component that has the very same closed
`Signal.register init x` (equal hardware, so the same register), when there is one.  Nothing else changes: the registers stay all taken (the
replaced register keeps its earlier taker).  The stored statement does not contain `R`; the proof still compares every register's equation.
-/

namespace Tools.VedMemS94Inv

open Lean Meta

/-- option `ved.mem.s94PairFix` (default false): `repairShared` after the old pairing -/
register_option ved.mem.s94PairFix : Bool := {
  defValue := false
  descr := "invariant R: components sharing a register with an earlier component are re-paired by equal closed hardware (Tools.VedMemS94Inv)"
}

/-- test seam / diagnosis: number of components re-paired by the last call -/
initialize pairFixCount : IO.Ref Nat ← IO.mkRef 0

private def nameIs (e : Expr) (s : String) : Bool :=
  match e.getAppFn.constName? with
  | some n => n.isStr && n.getString! == s
  | none => false

/-- the `Signal.register init x` leaves of a bundle `bundle2 a (bundle2 b ..)`, in component order; `some key` (the whole `Signal.register init x`)
when the register does not mention `loop` (the loop's own value, the state of the body), else `none`; `none` overall for a shape it does not know -/
partial def regKeys (loop : Expr) (e : Expr) (fuel : Nat := 8) : MetaM (Option (List (Option Expr))) := do
  let e := (← instantiateMVars e).consumeMData.headBeta
  let n := e.getAppNumArgs
  if nameIs e "bundle2" && n ≥ 2 then
    let some l ← regKeys loop (e.getArg! (n - 2)) fuel | return none
    let some r ← regKeys loop (e.getArg! (n - 1)) fuel | return none
    return some (l ++ r)
  if nameIs e "register" && n ≥ 2 then
    let closed := (e.find? (· == loop)).isNone && !e.hasLooseBVars
    return some [if closed then some e else none]
  if fuel > 0 then
    if let some u ← unfoldDefinition? e then return ← regKeys loop u (fuel - 1)
  return none

/-- the keys of one `Signal.loop` term -/
def loopKeys (loop : Expr) : MetaM (Option (List (Option Expr))) := do
  let args := loop.getAppArgs
  let some f := args[3]? | return none
  let body := match f with
    | .lam _ _ b _ => b.instantiate1 loop
    | f => (mkApp f loop).headBeta
  regKeys loop (← instantiateMVars (← zetaReduce body))

/-- the repair; `keys`, `widths`, `names` aligned per component (all loops, in order); `names` the old pairing -/
def repairShared (keys : List (Option Expr)) (names : List String) : List String := Id.run do
  let ks := keys.toArray
  let mut out := names.toArray
  for k in [0:ks.size] do
    let some key := ks[k]! | continue
    let mine := out[k]!
    -- a share of the old pairing: the register is taken by an earlier component
    unless (List.range k).any (fun i => out[i]! == mine) do continue
    -- the old partner(s) of the share already have this closed key: nothing to repair
    if (List.range k).any (fun i => out[i]! == mine && ks[i]! == some key) then continue
    -- the earliest component with the same closed hardware
    match (List.range k).find? (fun j => ks[j]! == some key) with
    | some j => out := out.set! k out[j]!
    | none => pure ()
  return out.toList

/-- the hunk of `buildR`: the old pairing `names` of the components of `loops` (`compsOf[j]` the state components of loop `j`), repaired when the option is on.
Env `VED_PAIR_DIAG=1`: one line per loop (components, registers found) and per re-paired component on stderr (diagnosis). -/
def pairFix (loops : Array Expr) (compsOf : Array (List Expr)) (names : List String) : MetaM (List String) := do
  let diag := (← IO.getEnv "VED_PAIR_DIAG").isSome
  unless diag || ved.mem.s94PairFix.get (← getOptions) do return names
  let mut keys : List (Option Expr) := []
  let mut ok := true
  for j in [0:loops.size] do
    match ← loopKeys loops[j]! with
    | some ks =>
      if diag then IO.eprintln s!"PAIR loop {j}: comps={compsOf[j]!.length} registers found={ks.length} closed={(ks.filter Option.isSome).length}"
      if ks.length == compsOf[j]!.length then keys := keys ++ ks
      else
        ok := false
        keys := keys ++ (compsOf[j]!.map fun _ => none)
    | none =>
      if diag then IO.eprintln s!"PAIR loop {j}: shape not recognised"
      ok := false
      keys := keys ++ (compsOf[j]!.map fun _ => none)
  let new := repairShared keys names
  if diag then
    for (a, b) in (List.range names.length).zip (names.zip new) do
      if b.1 != b.2 then IO.eprintln s!"PAIR comp {a}: {b.1} -> {b.2}"
    for r in (names.eraseDups) do
      let cs := (List.range names.length).filter fun i => names[i]! == r
      if cs.length > 1 then IO.eprintln s!"PAIR share {r}: comps {cs} closed keys {cs.map fun i => (keys[i]!).isSome}"
    IO.eprintln s!"PAIR done ok={ok} comps={names.length} changed={(names.zip new).filter (fun p => p.1 != p.2) |>.length}"
  -- a loop whose shape is not recognised contributes no key (its components are never re-paired)
  if !ved.mem.s94PairFix.get (← getOptions) then return names
  pairFixCount.set ((← pairFixCount.get) + ((names.zip new).filter fun p => p.1 != p.2).length)
  return new

end Tools.VedMemS94Inv
