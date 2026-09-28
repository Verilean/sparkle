import Tools.ShippingOptSoundness
import Tools.SVParser.EmitSem

/-! # Shipping expression text and the semantic SV tree

The renderer below consumes the SV AST, not the IR. On the supported binary-operator
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
  | .shr => some ">>"
  | .shl => some "<<"
  | .eq => some "==" | .lt => some "<" | .le => some "<="
  | .gt => some ">" | .ge => some ">="
  | _ => none

/-- Literal rendering shared by the leaf and concatenation arms. -/
def renderLit : SVLiteral → Option String
  | .decimal (some w) v => if w = 0 then none else some s!"{w}'d{v}"
  | .hex (some w) v => if w = 0 then none else some s!"{w}'h{String.ofList (Nat.toDigits 16 v)}"
  | .binary (some 1) 0 => some "1'b0"
  | _ => none

/-- A deliberately small, total AST renderer. Unsupported forms fail.
Concatenation is restricted to the emitted zero-extension shape, a literal
prefix over an identifier. -/
def renderExpr : SVExpr → Option String
  | .lit l => renderLit l
  | .unary .signed a => do
    let sa ← renderExpr a
    some s!"$signed({sa})"
  | .ident n => some n
  | .binary op a b => do
    let tok ← renderBin op
    let sa ← renderExpr a
    let sb ← renderExpr b
    some s!"({sa} {tok} {sb})"
  | .ternary c t f => do
    let sc ← renderExpr c
    let st ← renderExpr t
    let sf ← renderExpr f
    some s!"({sc} ? {st} : {sf})"
  | .concat [.lit l, .ident n] => do
    let sa ← renderLit l
    some s!"\{{String.intercalate ", " [sa, n]}}"
  | .sizeCast w a =>
    if w = 0 then none else do
      let sa ← renderExpr a
      some s!"{w}'({sa})"
  | _ => none

/-- Comparison operators, independent of optimizer acceptance. -/
abbrev isCompareOp : Operator → Bool := isControlBinOp

/-- Byte rendering needs no numerical fit premise. Negative constants are
printed in hexadecimal by the shipping emitter; this is separate from the
stronger hypotheses needed for SV evaluation. -/
inductive PrintShape : Expr → Prop
  | const (v : Int) (w : Nat) : PrintShape (.const v w)
  | ref (x : String) : PrintShape (.ref x)
  | bin {o : Operator} {a b : Expr} : isPrintBinOp o = true → PrintShape a → PrintShape b →
      PrintShape (.op o [a, b])
  | compare {o : Operator} {a b : Expr} : isCompareOp o = true → PrintShape a → PrintShape b →
      PrintShape (.op o [a, b])
  | mux {c t f : Expr} : PrintShape c → PrintShape t → PrintShape f →
      PrintShape (.op .mux [c, t, f])
  /-- Zero-extension: a constant prefix over a wire, `{k'dv, x}`. -/
  | zext (v : Int) (k : Nat) (x : String) : PrintShape (.concat [.const v k, .ref x])
  /-- The canonical size-cast encode, printed as `w'(x)`. -/
  | castRef (x : String) (w : Nat) : 0 < w →
      PrintShape (.slice (.concat [.const 0 w, .ref x]) (w - 1) 0)

theorem PrintShape.ofShape {e : Expr} (h : Shape e) : PrintShape e := by
  induction h with
  | const _ _ => exact .const _ _
  | ref x => exact .ref x
  | bin ho _ _ ha hb => exact .bin (by simp [isPrintBinOp, ho]) ha hb

theorem printShape_simple {e : Expr} (h : simpleRhs e = true) : PrintShape e := by
  match e, h with
  | .const v w, _ => exact .const v w
  | .ref x, _ => exact .ref x
  | .op o [.ref a, .ref b], h =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact .bin h (.ref a) (.ref b)
    · exact .compare h (.ref a) (.ref b)
  | .op .mux [.ref c, .ref t, .ref f], _ => exact .mux (.ref c) (.ref t) (.ref f)
  | .concat [.const v k, .ref x], _ => exact .zext v k x
  | .slice (.concat [.const 0 w, .ref x]) hi lo, h =>
    simp only [simpleRhs, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hlo, hhi⟩ := h
    subst hlo
    have shape := PrintShape.castRef x w (by omega)
    rwa [show w - 1 = hi from by omega] at shape

/-- Width inference agrees for the whole printable expression fragment. -/
theorem PrintShape.width_lookup {e : Expr} (h : PrintShape e) (wof : String → Option Nat) :
    exprWidthT wof e = Sparkle.Backend.Verilog.exprWidthV wof e := by
  induction h with
  | const | ref => simp [exprWidthT, Sparkle.Backend.Verilog.exprWidthV]
  | @bin op a b hop _ _ ia ib =>
    cases op <;> simp_all [isPrintBinOp_eq_true, isBinOp]
    all_goals
      simp only [exprWidthT, exprWidthT.goMax, Sparkle.Backend.Verilog.exprWidthV,
        List.foldl_cons, List.foldl_nil, ia, ib]
    all_goals
      cases Sparkle.Backend.Verilog.exprWidthV wof a <;>
        cases Sparkle.Backend.Verilog.exprWidthV wof b <;> simp [Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  | compare hop => cases ‹Operator› <;> simp_all [isCompareOp, isControlBinOp, exprWidthT, Sparkle.Backend.Verilog.exprWidthV]
  | @mux c t f _ _ _ _ it iff =>
    simp only [exprWidthT, Sparkle.Backend.Verilog.exprWidthV, it, iff]
    cases Sparkle.Backend.Verilog.exprWidthV wof t <;> cases Sparkle.Backend.Verilog.exprWidthV wof f <;> rfl
  | zext v k x =>
    simp only [exprWidthT, exprWidthT.goSum, Sparkle.Backend.Verilog.exprWidthV,
      List.foldl_cons, List.foldl_nil]
    cases wof x <;> simp
  | castRef x w hw =>
    simp [exprWidthT, Sparkle.Backend.Verilog.exprWidthV]

theorem render_const (wof : String → Option Nat) (v : Int) (w : Nat) :
    ∃ l, emitAstExpr wof (.const v w) = some (.lit l) ∧
      renderLit l = some (Sparkle.Backend.Verilog.emitExpr wof (.const v w)) := by
  have hw : (if w = 0 then 1 else w) ≠ 0 := by split <;> simp_all
  cases v with
  | ofNat v =>
    refine ⟨.decimal (some (if w == 0 then 1 else w)) v, ?_, ?_⟩
    · simp [emitAstExpr]
    · simp [renderLit, hw, Sparkle.Backend.Verilog.emitExpr, Int.repr]
      intro hneg; omega
  | negSucc v =>
    have hn : Int.negSucc v < 0 := by omega
    refine ⟨.hex (some (if w == 0 then 1 else w))
      (encodeConst (Int.negSucc v) (if w == 0 then 1 else w)), ?_, ?_⟩
    · simp [emitAstExpr, hn]
    · simp [renderLit, hw, Sparkle.Backend.Verilog.emitExpr, hn, encodeConst]

theorem emitExpr_render_all {e : Expr} (h : PrintShape e) (wof : String → Option Nat) :
    ∃ sv, emitAstExpr wof e = some sv ∧
      renderExpr sv = some (Sparkle.Backend.Verilog.emitExpr wof e) := by
  induction h with
  | const v w =>
    obtain ⟨l, he, hr⟩ := render_const wof v w
    exact ⟨.lit l, he, hr⟩
  | ref x => exact ⟨.ident _, rfl, by simp [renderExpr, Sparkle.Backend.Verilog.emitExpr]⟩
  | @bin op a b hop _ _ ia ib =>
    obtain ⟨sa, hsa, hra⟩ := ia
    obtain ⟨sb, hsb, hrb⟩ := ib
    cases op <;> simp_all [isPrintBinOp_eq_true, isBinOp]
    all_goals
      simp [emitAstExpr, hsa, hsb, binOpOf, renderExpr, renderBin, hra, hrb,
        Sparkle.Backend.Verilog.emitExpr, Sparkle.Backend.Verilog.emitOperator]

  | @compare op a b hop ha hb ia ib =>
    have wa := ha.width_lookup wof
    have wb := hb.width_lookup wof
    obtain ⟨sa, hsa, hra⟩ := ia
    obtain ⟨sb, hsb, hrb⟩ := ib
    cases op <;> simp_all [isCompareOp, isControlBinOp]
    all_goals
      simp only [emitAstExpr, hsa, hsb, bind, Option.bind_some, wa, wb]
      cases wa' : Sparkle.Backend.Verilog.exprWidthV wof a <;>
        cases wb' : Sparkle.Backend.Verilog.exprWidthV wof b <;>
        simp [wa', wb', binOpOf, renderExpr, renderLit, renderBin, hra, hrb,
          Sparkle.Backend.Verilog.emitExpr, Sparkle.Backend.Verilog.emitOperator]
      all_goals try split
      all_goals simp_all [renderExpr, renderLit, renderBin, hra, hrb,
        String.append_assoc, ToString.toString]
      all_goals try simp_all only [← not_and]
      all_goals try simp_all only [ite_false, Option.bind_some, Option.some.injEq]
      all_goals
        apply String.toList_injective
        simp only [String.toList_append, List.append_assoc]
        rfl
  | mux _ _ _ ic it iff =>
    obtain ⟨sc, hsc, hrc⟩ := ic
    obtain ⟨st, hst, hrt⟩ := it
    obtain ⟨sf, hsf, hrf⟩ := iff
    exact ⟨.ternary sc st sf, by simp [emitAstExpr, hsc, hst, hsf],
      by simp [renderExpr, hrc, hrt, hrf, Sparkle.Backend.Verilog.emitExpr]⟩
  | zext v k x =>
    obtain ⟨l, hsl, hrl⟩ := render_const wof v k
    have hstr : Sparkle.Backend.Verilog.emitExpr wof (.concat [.const v k, .ref x]) =
        s!"\{{String.intercalate ", " [Sparkle.Backend.Verilog.emitExpr wof (.const v k),
          Sparkle.Backend.Verilog.sanitizeName x]}}" := by
      simp only [Sparkle.Backend.Verilog.emitExpr, List.attach, List.attachWith,
        List.map_cons, List.map_nil, List.pmap]
    refine ⟨.concat [.lit l, .ident (Sparkle.Backend.Verilog.sanitizeName x)], ?_, ?_⟩
    · simp only [emitAstExpr, Tools.SVParser.EmitAst.emitConcatElems, bind] at hsl ⊢
      rw [hsl]
      rfl
    · rw [hstr]
      simp only [renderExpr, hrl, bind, Option.bind_some]
  | castRef x w hw =>
    have harm : ((0 == 0 : Bool) && (w - 1 + 1 == w)) = true := by
      simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
      omega
    have hstr : Sparkle.Backend.Verilog.emitExpr wof
        (.slice (.concat [.const 0 w, .ref x]) (w - 1) 0) =
        s!"{w}'({Sparkle.Backend.Verilog.sanitizeName x})" := by
      simp only [Sparkle.Backend.Verilog.emitExpr, harm, if_true]
    refine ⟨.sizeCast w (.ident (Sparkle.Backend.Verilog.sanitizeName x)), ?_, ?_⟩
    · simp only [emitAstExpr, harm, if_true, bind, Option.bind_some]
    · have hw' : ¬ w = 0 := by omega
      rw [hstr]
      simp only [renderExpr, hw', if_false, bind, Option.bind_some]

/-- Arbitrarily nested expressions, including optimizer-inserted masks. -/
theorem emitExpr_render {e : Expr} (h : Shape e) (wof : String → Option Nat) :
    ∃ sv, emitAstExpr wof e = some sv ∧
      renderExpr sv = some (Sparkle.Backend.Verilog.emitExpr wof e) := by
  induction h with
  | @const v w h0 hlt =>
    have hw : (if w = 0 then 1 else w) ≠ 0 := by split <;> simp_all
    have hn : ¬ v < 0 := by omega
    refine ⟨.lit (.decimal (some (if w == 0 then 1 else w)) v.toNat), ?_, ?_⟩
    · simp [emitAstExpr, hn]
    · cases v with
      | ofNat v =>
        simp [renderExpr, renderLit, hw, Sparkle.Backend.Verilog.emitExpr, Int.repr]
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

theorem emitStmt_render_all {e : Expr} (h : PrintShape e) (lhs indent : String)
    (wires : List Port) :
    ∃ item, emitAstStmt (printWidths wires) wires (.assign lhs e) = some [item] ∧
      renderItem indent item = some (Sparkle.Backend.Verilog.emitStmt (.assign lhs e) indent wires) := by
  obtain ⟨sv, hs, hr⟩ := emitExpr_render_all h (printWidths wires)
  refine ⟨.contAssign (.ident (Sparkle.Backend.Verilog.sanitizeName lhs)) sv, ?_, ?_⟩
  · simp [emitAstStmt, hs]
  · simp [renderItem, hr, Sparkle.Backend.Verilog.emitStmt]
    rfl

theorem checkedOptimize_printShape {m : Sparkle.IR.AST.Module} (hgate : simpleBody m = true) :
    ∀ st ∈ (checkedOptimize m).body, ∃ l r, st = .assign l r ∧ PrintShape r := by
  unfold checkedOptimize
  simp only [hgate, if_true]
  split
  · rename_i hc
    have hc := (Bool.and_eq_true_iff.mp hc).1
    have hc := (Bool.and_eq_true_iff.mp hc).1
    unfold optCheckCore at hc
    dsimp only at hc
    split at hc
    · rename_i dm ds hm ho
      intro st hs
      obtain ⟨l, r, he, hr⟩ := normBody_input_shape _ _ _ _ _ ho st hs
      exact ⟨l, r, he, PrintShape.ofShape hr⟩
    · cases hc
  · intro st hs
    have hr := List.all_eq_true.mp hgate st hs
    cases st with
    | assign l r => exact ⟨l, r, rfl, printShape_simple hr⟩
    | _ => cases hr

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
  have h := (Bool.and_eq_true_iff.mp h).1
  unfold optCheckCore at h
  dsimp only at h
  split at h
  · rename_i dm ds hm ho
    exact emitBody_render _ _ _ (normBody_input_shape _ _ _ _ _ ho)
  · cases h

/-- The semantic normalizer still refuses logical shifts. Expanding the shipping
checked-route domain does not silently expand the trusted normalization rules. -/
theorem normBody_shift_none {body : List Stmt} {l : String} {a b : Expr} {op : Operator}
    (hop : op = .shr ∨ op = .shl) (hm : .assign l (.op op [a, b]) ∈ body)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normBody we ins defs body = none := by
  induction body generalizing defs with
  | nil => cases hm
  | cons st rest ih =>
    rcases List.mem_cons.mp hm with he | htail
    · subst st; rcases hop with rfl | rfl <;> simp [normBody, normE, isBinOp]
    · cases st with
      | assign l r =>
        simp only [normBody]
        cases he : normE we ins defs r with
        | none => rfl
        | some e => exact ih htail _
      | _ => rfl

theorem normBody_shr_none {body : List Stmt} {l : String} {a b : Expr}
    (hm : .assign l (.op .shr [a, b]) ∈ body)
    (we : WEnv) (ins : List String) (defs : List (String × Expr)) :
    normBody we ins defs body = none :=
  normBody_shift_none (Or.inl rfl) hm we ins defs

/-- Shift-bearing simple modules now take the proved original-module fallback.
The full optimizer's shift rewrites remain proposals, not trusted proof steps. -/
theorem checkedOptimize_shr {m : Sparkle.IR.AST.Module} {l : String} {a b : Expr}
    (hg : simpleBody m = true) (hm : .assign l (.op .shr [a, b]) ∈ m.body) :
    checkedOptimize m = m := by
  have hnorm := normBody_shr_none hm (Sparkle.IR.RegDedup.declWidth m)
    (m.inputs.map (·.name)) []
  simp [checkedOptimize, hg, optCheck, optCheckCore, hnorm]

/-- The same checked fallback covers logical left shift. -/
theorem checkedOptimize_shl {m : Sparkle.IR.AST.Module} {l : String} {a b : Expr}
    (hg : simpleBody m = true) (hm : .assign l (.op .shl [a, b]) ∈ m.body) :
    checkedOptimize m = m := by
  have hnorm := normBody_shift_none (Or.inr rfl) hm (Sparkle.IR.RegDedup.declWidth m)
    (m.inputs.map (·.name)) []
  simp [checkedOptimize, hg, optCheck, optCheckCore, hnorm]

end Tools.ShippingPrintSoundness
