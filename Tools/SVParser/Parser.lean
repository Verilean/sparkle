/-
  SystemVerilog Parser — Recursive descent for synthesizable RTL
-/

import Tools.SVParser.AST
import Tools.SVParser.Lexer

open Tools.SVParser.AST
open Tools.SVParser.Lexer

namespace Tools.SVParser.Parser

-- All expression/statement parsers are mutually recursive via parseExpr
mutual

partial def parseExpr : P SVExpr := parseTernary

partial def parseTernary : P SVExpr := do
  let e ← parseLogOr
  match ← attempt qmark with
  | some _ => let t ← parseExpr; colon; let el ← parseExpr; pure (SVExpr.ternary e t el)
  | none => pure e

partial def parseLogOr : P SVExpr := do
  let mut e ← parseLogAnd
  let mut cont := true
  while cont do
    match ← attempt (op2 "||") with
    | some _ => let rhs ← parseLogAnd; e := SVExpr.binary .logOr e rhs
    | none => cont := false
  pure e

partial def parseLogAnd : P SVExpr := do
  let mut e ← parseBitOr
  let mut cont := true
  while cont do
    match ← attempt (op2 "&&") with
    | some _ => let rhs ← parseBitOr; e := SVExpr.binary .logAnd e rhs
    | none => cont := false
  pure e

partial def parseBitOr : P SVExpr := do
  let mut e ← parseBitXor
  let mut cont := true
  while cont do
    -- Match single | but not ||
    match ← attempt (do
      let _ ← token (matchStr "|")
      let next ← peekChar
      if next == some '|' then fail "||"
      pure ()) with
    | some _ => let rhs ← parseBitXor; e := SVExpr.binary .bitOr e rhs
    | none => cont := false
  pure e

partial def parseBitXor : P SVExpr := do
  let mut e ← parseBitAnd
  let mut cont := true
  while cont do
    match ← attempt (token (matchStr "^")) with
    | some _ => let rhs ← parseBitAnd; e := SVExpr.binary .bitXor e rhs
    | none => cont := false
  pure e

partial def parseBitAnd : P SVExpr := do
  let mut e ← parseEquality
  let mut cont := true
  while cont do
    match ← attempt (do
      let _ ← token (matchStr "&")
      let next ← peekChar
      if next == some '&' then fail "&&"
      pure ()) with
    | some _ => let rhs ← parseEquality; e := SVExpr.binary .bitAnd e rhs
    | none => cont := false
  pure e

partial def parseEquality : P SVExpr := do
  let mut e ← parseRelational
  let mut cont := true
  while cont do
    match ← attempt (op2 "!=") with
    | some _ => let rhs ← parseRelational; e := SVExpr.binary .neq e rhs
    | none =>
      match ← attempt (op2 "==") with
      | some _ => let rhs ← parseRelational; e := SVExpr.binary .eq e rhs
      | none => cont := false
  pure e

partial def parseRelational : P SVExpr := do
  let mut e ← parseShift
  let mut cont := true
  while cont do
    match ← attempt (op2 "<=") with
    | some _ => let rhs ← parseShift; e := SVExpr.binary .le e rhs
    | none =>
      match ← attempt (op2 ">=") with
      | some _ => let rhs ← parseShift; e := SVExpr.binary .ge e rhs
      | none =>
        match ← attempt (do let _ ← token (matchStr "<"); let next ← peekChar
                            if next == some '<' then fail "<<"; pure ()) with
        | some _ => let rhs ← parseShift; e := SVExpr.binary .lt e rhs
        | none =>
          match ← attempt (do let _ ← token (matchStr ">"); let next ← peekChar
                              if next == some '>' then fail ">>"; pure ()) with
          | some _ => let rhs ← parseShift; e := SVExpr.binary .gt e rhs
          | none => cont := false
  pure e

partial def parseShift : P SVExpr := do
  let mut e ← parseAdd
  let mut cont := true
  while cont do
    match ← attempt (op2 ">>>") with
    | some _ => let rhs ← parseAdd; e := SVExpr.binary .asr e rhs
    | none =>
      match ← attempt (op2 "<<") with
      | some _ => let rhs ← parseAdd; e := SVExpr.binary .shl e rhs
      | none =>
        match ← attempt (op2 ">>") with
        | some _ => let rhs ← parseAdd; e := SVExpr.binary .shr e rhs
        | none => cont := false
  pure e

partial def parseAdd : P SVExpr := do
  let mut e ← parseMul
  let mut cont := true
  while cont do
    match ← attempt (token (matchStr "+")) with
    | some _ => let rhs ← parseMul; e := SVExpr.binary .add e rhs
    | none =>
      match ← attempt (do let _ ← token (matchStr "-"); parseMul) with
      | some rhs => e := SVExpr.binary .sub e rhs
      | none => cont := false
  pure e

partial def parseMul : P SVExpr := do
  let mut e ← parseUnary
  let mut cont := true
  while cont do
    match ← attempt (token (matchStr "*")) with
    | some _ => let rhs ← parseUnary; e := SVExpr.binary .mul e rhs
    | none => cont := false
  pure e

partial def parseUnary : P SVExpr := do
  let c ← peekChar
  match c with
  | some '!' => let _ ← token (matchStr "!"); let e ← parseUnary; pure (SVExpr.unary .logNot e)
  | some '~' => let _ ← token (matchStr "~"); let e ← parseUnary; pure (SVExpr.unary .bitNot e)
  | _ => parsePrimaryPost

partial def parsePrimaryPost : P SVExpr := do
  let e ← parsePrimary
  parsePostfix e

partial def parsePostfix (e : SVExpr) : P SVExpr := do
  match ← attempt lbracket with
  | some _ =>
    let idx ← token digits
    match ← attempt colon with
    | some _ =>
      let lo ← token digits; rbracket
      parsePostfix (SVExpr.slice e idx.toNat! lo.toNat!)
    | none =>
      rbracket
      parsePostfix (SVExpr.index e (SVExpr.lit (SVLiteral.decimal none idx.toNat!)))
  | none => pure e

partial def parsePrimary : P SVExpr := do
  let c ← peekChar
  match c with
  | some '{' =>
    lbrace; let first ← parseExpr
    let mut args := [first]
    let mut cont := true
    while cont do
      match ← attempt comma with
      | some _ => let e ← parseExpr; args := args ++ [e]
      | none => cont := false
    rbrace; pure (SVExpr.concat args)
  | some '(' => lparen; let e ← parseExpr; rparen; pure e
  | some c' =>
    if isDigit c' then let lit ← numericLiteral; pure (SVExpr.lit lit)
    else if isAlpha c' then let name ← identifier; pure (SVExpr.ident name)
    else fail s!"unexpected char in expression: '{c'}'"
  | none => fail "unexpected end of input in expression"

-- Statement parsing
partial def parseStmtList : P (List SVStmt) := do
  match ← attempt (keyword "begin") with
  | some _ =>
    let stmts ← many parseStmt
    keyword "end"; pure stmts.toList
  | none => let s ← parseStmt; pure [s]

partial def parseStmt : P SVStmt := do
  match ← attempt (keyword "if") with
  | some _ =>
    lparen; let cond ← parseExpr; rparen
    let thenB ← parseStmtList
    let elseB ← match ← attempt (keyword "else") with
      | some _ => parseStmtList | none => pure []
    pure (SVStmt.ifElse cond thenB elseB)
  | none =>
    match ← attempt (keyword "case") with
    | some _ =>
      lparen; let expr ← parseExpr; rparen
      let mut arms : List (SVExpr × List SVStmt) := []
      let mut default_ : Option (List SVStmt) := none
      let mut cont := true
      while cont do
        match ← attempt (keyword "endcase") with
        | some _ => cont := false
        | none =>
          match ← attempt (keyword "default") with
          | some _ => colon; let stmts ← parseStmtList; default_ := some stmts
          | none =>
            let label ← parseExpr; colon; let stmts ← parseStmtList
            arms := arms ++ [(label, stmts)]
      pure (SVStmt.caseStmt expr arms default_)
    | none => parseAssignStmt

partial def parseAssignStmt : P SVStmt := do
  -- Try non-blocking first: ident <= expr ;
  match ← attempt (do
    let lhs ← parsePrimaryPost  -- just ident or ident[idx]
    op2 "<="
    let rhs ← parseExpr
    semi
    pure (SVStmt.nonblockAssign lhs rhs)) with
  | some s => pure s
  | none =>
    -- Blocking: expr = expr ;
    let lhs ← parsePrimaryPost
    eqSign; let rhs ← parseExpr; semi
    pure (SVStmt.blockAssign lhs rhs)

end -- mutual

-- ============================================================================
-- Module-level (not mutually recursive with expressions)
-- ============================================================================

def parsePortDir : P SVPortDir := do
  match ← attempt (keyword "input") with
  | some _ => pure .input
  | none => match ← attempt (keyword "output") with
    | some _ => pure .output
    | none => keyword "inout"; pure .inout

def parseOptWidth : P (Option (Nat × Nat)) := do
  match ← attempt bitRange with
  | some r => pure (some r) | none => pure none

def parsePortInList : P SVPort := do
  let dir ← parsePortDir
  let _ ← attempt (keyword "logic")
  let _ ← attempt (keyword "reg")
  let _ ← attempt (keyword "wire")
  let width ← parseOptWidth
  let name ← identifier
  pure { dir, width, name }

def parsePortList : P (List SVPort) := do
  lparen; let first ← parsePortInList
  let rest ← many (do comma; parsePortInList)
  rparen; pure (first :: rest.toList)

def parseSensitivity : P SVSensitivity := do
  match ← attempt (keyword "posedge") with
  | some _ => let s ← identifier; pure (SVSensitivity.posedge s)
  | none => match ← attempt (keyword "negedge") with
    | some _ => let s ← identifier; pure (SVSensitivity.negedge s)
    | none => let _ ← token (matchStr "*"); pure SVSensitivity.star

partial def parseAlwaysBlock : P SVModuleItem := do
  keyword "always"
  let _ ← attempt (matchStr "_ff")
  let _ ← attempt (matchStr "_comb")
  ws; at_; lparen
  let sens ← parseSensitivity
  let _ ← many (do keyword "or"; let _ ← parseSensitivity; pure ())
  rparen; keyword "begin"
  let stmts ← many parseStmt
  keyword "end"
  pure (SVModuleItem.alwaysBlock sens stmts.toList)

partial def parseModuleItem : P SVModuleItem := do
  match ← attempt (keyword "assign") with
  | some _ =>
    let lhs ← parseExpr; eqSign; let rhs ← parseExpr; semi
    pure (SVModuleItem.contAssign lhs rhs)
  | none => match ← attempt (keyword "wire") with
    | some _ =>
      let _ ← attempt (keyword "logic"); let w ← parseOptWidth
      let n ← identifier; semi; pure (SVModuleItem.wireDecl n w)
    | none => match ← attempt (keyword "reg") with
      | some _ =>
        let w ← parseOptWidth; let n ← identifier; semi
        pure (SVModuleItem.regDecl n w)
      | none => parseAlwaysBlock

partial def parseModule : P SVModule := do
  keyword "module"; let name ← identifier; let ports ← parsePortList; semi
  let items ← many parseModuleItem
  keyword "endmodule"
  pure { name, ports, items := items.toList }

-- ============================================================================
-- Public API
-- ============================================================================

def parse (input : String) : Except String SVDesign :=
  Lexer.run (do ws; let modules ← many1 parseModule; pure { modules := modules.toList }) input

def parseModuleFromString (input : String) : Except String SVModule :=
  Lexer.run (do ws; parseModule) input

end Tools.SVParser.Parser
