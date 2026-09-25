import Tools.ShippingOptSoundness
import Tools.SVParser.EmitSem

/-! # Shipping expression text and the semantic SV tree

The renderer below consumes the SV AST, not the IR. On the six-operator
fragment, rendering `emitAstExpr` is proved equal to the SHIPPING `emitExpr`.
This is a byte equality, not a parser experiment. `printedExpr_semantics`
also connects that same tree to the existing SV-subset evaluation theorem.

`ShippingModulePrintSoundness` extends byte equality to declarations and full
module text. Identifier legality remains separate. In particular, sanitize-fixed
names need not be legal SV identifiers (digits at the start and keywords).
No parser correctness or identifier legality is asserted by byte equality.
-/

namespace Tools.ShippingPrintSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.ShippingOptSoundness
open Sparkle.IR.OptCheck

/-- Acceptance by the shipping optimizer's normalizer implies that the
ORIGINAL expression, not only its normal form, is in the printable grammar. -/
theorem normE_input_shape (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    ∀ e r, normE we ins defs e = some r → Shape e
  | .const v w, _, h => by
    simp only [normE] at h
    split at h
    · rename_i hc; exact .const hc.1 hc.2
    · cases h
  | .ref x, _, _ => .ref x
  | .op o [a, b], _, h => by
    simp only [normE] at h
    split at h
    · rename_i ho
      cases ha : normE we ins defs a with
      | none => simp [ha] at h
      | some a' =>
        cases hb : normE we ins defs b with
        | none => simp [ha, hb] at h
        | some b' =>
          exact .bin ho (normE_input_shape we ins defs a a' ha)
            (normE_input_shape we ins defs b b' hb)
    · cases h
  | .op _ [], _, h | .op _ [_], _, h | .op _ (_ :: _ :: _ :: _), _, h => by
    simp [normE] at h
  | .concat _, _, h | .slice .., _, h | .sliceDim .., _, h | .index .., _, h => by
    simp [normE] at h

theorem normBody_input_shape (we : WEnv) (ins : List String) :
    ∀ body defs result, normBody we ins defs body = some result →
      ∀ st ∈ body, ∃ lhs rhs, st = .assign lhs rhs ∧ Shape rhs
  | [], _, _, _, _, h => by cases h
  | .assign l r :: rest, defs, result, h, st, hs => by
    simp only [normBody] at h
    cases he : normE we ins defs r with
    | none => simp [he] at h
    | some e =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      rcases List.mem_cons.mp hs with hst | hst
      · subst st; exact ⟨l, r, rfl, normE_input_shape we ins defs r e he⟩
      · exact normBody_input_shape we ins rest _ result h st hst
  | .register .. :: _, _, _, h, _, _
  | .memory .. :: _, _, _, h, _, _
  | .inst .. :: _, _, _, h, _, _ => by simp [normBody] at h

def renderBin : SVBinOp → Option String
  | .add => some "+" | .sub => some "-" | .mul => some "*"
  | .bitAnd => some "&" | .bitOr => some "|" | .bitXor => some "^"
  | _ => none

/-- A deliberately small, total AST renderer. Unsupported forms fail. -/
def renderExpr : SVExpr → Option String
  | .lit (.decimal (some w) v) => some s!"{w}'d{v}"
  | .ident n => some n
  | .binary op a b => do
    let tok ← renderBin op
    let sa ← renderExpr a
    let sb ← renderExpr b
    some s!"({sa} {tok} {sb})"
  | _ => none

/-- Arbitrarily nested expressions, including optimizer-inserted masks. -/
theorem emitExpr_render {e : Expr} (h : Shape e) (wof : String → Option Nat) :
    ∃ sv, emitAstExpr wof e = some sv ∧
      renderExpr sv = some (Sparkle.Backend.Verilog.emitExpr wof e) := by
  induction h with
  | @const v w h0 hlt =>
    have hn : ¬ v < 0 := by omega
    refine ⟨.lit (.decimal (some (if w == 0 then 1 else w)) v.toNat), ?_, ?_⟩
    · simp [emitAstExpr, hn]
    · cases v with
      | ofNat v =>
        simp [renderExpr, Sparkle.Backend.Verilog.emitExpr, Int.repr]
        intro hneg
        omega
      | negSucc v => omega
  | ref x =>
    exact ⟨.ident _, rfl, by simp [renderExpr, Sparkle.Backend.Verilog.emitExpr]⟩
  | @bin op a b hop ha hb ia ib =>
    obtain ⟨sa, hsa, hra⟩ := ia
    obtain ⟨sb, hsb, hrb⟩ := ib
    cases op <;> simp_all [Sparkle.IR.OptCheck.isBinOp]
    all_goals
      simp [emitAstExpr, hsa, hsb, binOpOf, renderExpr, renderBin, hra, hrb,
        Sparkle.Backend.Verilog.emitExpr, Sparkle.Backend.Verilog.emitOperator]

/-- The tree whose rendering is the actual printed expression computes the
IR value. Width/boundedness hypotheses are the existing SV fragment's, not
a claim that arbitrary mixed-width expressions are safe. -/
theorem printedExpr_semantics {e : Expr} (hshape : Shape e)
    {wof : String → Option Nat} {we : WEnv} {env : Env}
    (hcheck : sf4Check wof we e = true) (hbe : Bounded we env)
    (hbw : ∀ n wn, wof n = some wn → env n < 2 ^ wn) :
    ∃ sv, emitAstExpr wof e = some sv ∧
      renderExpr sv = some (Sparkle.Backend.Verilog.emitExpr wof e) ∧
      Tools.SVParser.SVSemantics.evalSV wof env (widthOf we e) sv = evalExpr we env e := by
  obtain ⟨sv, hs, hr⟩ := emitExpr_render hshape wof
  exact ⟨sv, hs, hr, emit_sem_evalSV (sf4Check_sound hcheck) hbe hbw hs⟩

/-- The width lookup used by the shipping statement printer. -/
def printWidths (wires : List Port) (n : String) : Option Nat :=
  (wires.find? (fun p => Sparkle.Backend.Verilog.sanitizeName p.name == n)).bind fun p =>
    match p.ty with
    | .bitVector w => some w
    | .bit => some 1
    | _ => none

def renderItem (indent : String) : SVModuleItem → Option String
  | .contAssign (.ident lhs) rhs => do
    let text ← renderExpr rhs
    some s!"{indent}assign {lhs} = {text};"
  | _ => none

theorem emitStmt_render {e : Expr} (h : Shape e) (lhs indent : String)
    (wires : List Port) :
    ∃ item, emitAstStmt (printWidths wires) wires (.assign lhs e) = some [item] ∧
      renderItem indent item = some (Sparkle.Backend.Verilog.emitStmt (.assign lhs e) indent wires) := by
  obtain ⟨sv, hs, hr⟩ := emitExpr_render h (printWidths wires)
  refine ⟨.contAssign (.ident (Sparkle.Backend.Verilog.sanitizeName lhs)) sv, ?_, ?_⟩
  · simp [emitAstStmt, hs]
  · simp [renderItem, hr, Sparkle.Backend.Verilog.emitStmt]
    rfl

/-- This is the emitted continuous-assignment body, not a module header or
declaration renderer. Each item is tied to `emitAstStmt`. -/
def renderItems (indent : String) (items : List SVModuleItem) : Option String := do
  let texts ← items.mapM (renderItem indent)
  some (String.intercalate "\n\n" texts)

theorem emitBody_render (body : List Stmt) (indent : String) (wires : List Port)
    (hbody : ∀ st ∈ body, ∃ lhs rhs, st = .assign lhs rhs ∧ Shape rhs) :
    ∃ items, body.mapM (emitAstStmt (printWidths wires) wires) = some items ∧
      renderItems indent items.flatten =
        some (String.intercalate "\n\n" (body.map fun st =>
          Sparkle.Backend.Verilog.emitStmt st indent wires)) := by
  suffices h : ∃ items,
      body.mapM (emitAstStmt (printWidths wires) wires) = some items ∧
      items.flatten.mapM (renderItem indent) =
        some (body.map fun st => Sparkle.Backend.Verilog.emitStmt st indent wires) by
    obtain ⟨items, hi, hr⟩ := h
    exact ⟨items, hi, by simp [renderItems, hr]⟩
  induction body with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons st rest ih =>
    obtain ⟨lhs, rhs, rfl, h⟩ := hbody st (by simp)
    obtain ⟨item, hi, hr⟩ := emitStmt_render h lhs indent wires
    obtain ⟨items, his, hrs⟩ := ih (fun s hs => hbody s (by simp [hs]))
    refine ⟨[item] :: items, ?_, ?_⟩
    · simp [List.mapM_cons, hi, his]
    · simp [List.mapM_cons, hr, hrs]

/-- No new shape premise: a passing SHIPPING optimizer check supplies the
grammar needed to render every assignment of its proposed output. -/
theorem acceptedOptimizer_body_render {m o : Sparkle.IR.AST.Module}
    (h : optCheck m o = true) (indent : String) :
    ∃ items,
      o.body.mapM (emitAstStmt (printWidths (o.wires ++ o.inputs ++ o.outputs))
        (o.wires ++ o.inputs ++ o.outputs)) = some items ∧
      renderItems indent items.flatten = some (String.intercalate "\n\n"
        (o.body.map fun st => Sparkle.Backend.Verilog.emitStmt st indent
          (o.wires ++ o.inputs ++ o.outputs))) := by
  unfold optCheck at h
  dsimp only at h
  split at h
  · rename_i dm ds hm ho
    exact emitBody_render _ _ _ (normBody_input_shape _ _ _ _ _ ho)
  · cases h

end Tools.ShippingPrintSoundness
