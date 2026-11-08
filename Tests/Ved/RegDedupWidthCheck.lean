/-
  Regression for `Sparkle.IR.RegDedup.mergeDuplicates` (PR #147 review P1-1).

  Two nodes are merged only when they carry the same value at every
  cycle.  A register or wire truncates its input to its OWN width, so
  equal defining statements are not enough: an 8-bit and a 16-bit
  register of the same 16-bit input differ as soon as the input is
  ≥ 256.  Likewise an assignment `a := x` to a narrower wire is not a
  plain alias.  Each case below has a same-width control that IS merged,
  so the checks cannot pass by the pass doing nothing.
-/
import Sparkle.IR.RegDedup

namespace VedRegDedupWidth

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.RegDedup

/-- `n := r` appears in the body (n became an alias of r). -/
def aliased (m : Module) (n r : String) : Bool :=
  m.body.any fun st => match st with
    | .assign a (.ref b) => a == n && b == r
    | _ => false

def reg (o : String) (x : Expr) : Stmt := .register o "clk" ("rst", .synchronous) x 0

def mk (wires : List Port) (body : List Stmt) : Module :=
  { name := "t",
    inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"x", .bitVector 16⟩],
    outputs := [], wires := wires, body := body }

-- (1) registers of different widths, same clock/reset/init/input
def diffReg := mk [⟨"r8", .bitVector 8⟩, ⟨"r16", .bitVector 16⟩]
  [reg "r8" (.ref "x"), reg "r16" (.ref "x")]
#guard !(aliased (mergeDuplicates diffReg) "r16" "r8")
#guard (mergeDuplicates diffReg).body == diffReg.body
-- (1c) control: same width ⇒ merged
def sameReg := mk [⟨"r8", .bitVector 16⟩, ⟨"r16", .bitVector 16⟩]
  [reg "r8" (.ref "x"), reg "r16" (.ref "x")]
#guard aliased (mergeDuplicates sameReg) "r16" "r8"

-- (2) an alias through a NARROWER wire is not looked through
def narrowAlias := mk [⟨"a8", .bitVector 8⟩, ⟨"r1", .bitVector 16⟩, ⟨"r2", .bitVector 16⟩]
  [.assign "a8" (.ref "x"), reg "r1" (.ref "x"), reg "r2" (.ref "a8")]
#guard !(aliased (mergeDuplicates narrowAlias) "r2" "r1")
-- (2c) control: an alias of the same width is looked through ⇒ merged
def sameAlias := mk [⟨"a16", .bitVector 16⟩, ⟨"r1", .bitVector 16⟩, ⟨"r2", .bitVector 16⟩]
  [.assign "a16" (.ref "x"), reg "r1" (.ref "x"), reg "r2" (.ref "a16")]
#guard aliased (mergeDuplicates sameAlias) "r2" "r1"

-- (3) combinational wires of different widths with the same expression
def addX : Expr := .op .add [.ref "x", .ref "x"]
def diffAssign := mk [⟨"w8", .bitVector 8⟩, ⟨"w16", .bitVector 16⟩]
  [.assign "w8" addX, .assign "w16" addX]
#guard !(aliased (mergeDuplicates diffAssign) "w16" "w8")
-- (3c) control
def sameAssign := mk [⟨"w8", .bitVector 16⟩, ⟨"w16", .bitVector 16⟩]
  [.assign "w8" addX, .assign "w16" addX]
#guard aliased (mergeDuplicates sameAssign) "w16" "w8"

-- (4) `bit` and `bitVector 1` are kept apart (different declared types)
def bitVsBv1 := mk [⟨"b", .bit⟩, ⟨"v", .bitVector 1⟩]
  [reg "b" (.slice (.ref "x") 0 0), reg "v" (.slice (.ref "x") 0 0)]
#guard !(aliased (mergeDuplicates bitVsBv1) "v" "b")

-- (5) a symbolic width is never merged, even with an identical twin
def symW : HWType := .bitVectorDim (.parameter "W")
def symReg := mk [⟨"s1", symW⟩, ⟨"s2", symW⟩] [reg "s1" (.ref "x"), reg "s2" (.ref "x")]
#guard (mergeDuplicates symReg).body == symReg.body

-- (6) an undeclared node is never merged
def undeclared := mk [] [reg "u1" (.ref "x"), reg "u2" (.ref "x")]
#guard (mergeDuplicates undeclared).body == undeclared.body

end VedRegDedupWidth
