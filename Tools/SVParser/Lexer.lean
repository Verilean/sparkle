/-
  SystemVerilog Lexer — Simple recursive-descent tokenizer

  Parser state: (chars : Array Char) × (pos : Nat)
  The input string is converted to Array Char for O(1) indexing.
-/

import Tools.SVParser.AST

open Tools.SVParser.AST

namespace Tools.SVParser.Lexer

/-- Parser state: character array + position -/
structure PState where
  chars : Array Char
  pos   : Nat
  deriving Inhabited

/-- Parser monad: ExceptT over StateM for mut/while/for support -/
abbrev P (α : Type) := ExceptT String (StateM PState) α

def fail (msg : String) : P α := do
  let s ← get
  let near := String.ofList (s.chars.toList.drop s.pos |>.take 30)
  throw s!"at position {s.pos}: {msg} (near: \"{near}\")"

def getPos : P Nat := do let s ← get; pure s.pos

def atEnd : P Bool := do let s ← get; pure (s.pos ≥ s.chars.size)

def peekChar : P (Option Char) := do let s ← get; pure s.chars[s.pos]?

def nextChar : P Char := do
  let s ← get
  match s.chars[s.pos]? with
  | some c => set { s with pos := s.pos + 1 }; pure c
  | none => throw s!"unexpected end of input at position {s.pos}"

def setPos (pos : Nat) : P Unit := do let s ← get; set { s with pos }

/-- Try parser, backtrack on failure -/
def attempt (p : P α) : P (Option α) := do
  let s ← get
  try
    let a ← p; pure (some a)
  catch _ =>
    set s; pure none

-- ============================================================================
-- Character predicates
-- ============================================================================

def isAlpha (c : Char) : Bool := c.isAlpha || c == '_'
def isAlphaNum (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'
def isDigit (c : Char) : Bool := c.isDigit
def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == 'x' || c == 'X' || c == 'z' || c == 'Z'
def isBinDigit (c : Char) : Bool := c == '0' || c == '1' || c == 'x' || c == 'X' || c == 'z' || c == 'Z'

-- ============================================================================
-- Whitespace and comments
-- ============================================================================

partial def skipLineComment : P Unit := do
  let c ← peekChar
  match c with
  | some '\n' => let _ ← nextChar; pure ()
  | some _ => let _ ← nextChar; skipLineComment
  | none => pure ()

partial def skipBlockComment : P Unit := do
  let c ← nextChar
  if c == '*' then
    let next ← peekChar
    if next == some '/' then let _ ← nextChar
    else skipBlockComment
  else skipBlockComment

partial def ws : P Unit := do
  let c ← peekChar
  match c with
  | some ' ' | some '\n' | some '\r' | some '\t' =>
    let _ ← nextChar; ws
  | some '/' =>
    let savedPos ← getPos
    let _ ← nextChar
    let c2 ← peekChar
    if c2 == some '/' then let _ ← nextChar; skipLineComment; ws
    else if c2 == some '*' then let _ ← nextChar; skipBlockComment; ws
    else setPos savedPos  -- not a comment, restore
  | _ => pure ()

-- ============================================================================
-- Token helpers
-- ============================================================================

def token (p : P α) : P α := do let v ← p; ws; pure v

def matchStr (s : String) : P Unit := do
  let st ← get
  let sChars := s.toList
  let mut pos := st.pos
  for c in sChars do
    match st.chars[pos]? with
    | some c' => if c == c' then pos := pos + 1
                 else throw s!"expected '{s}' at position {st.pos}"
    | none => throw s!"expected '{s}' at position {st.pos}, got end of input"
  set { st with pos }

def keyword (kw : String) : P Unit := token do
  matchStr kw
  let c ← peekChar
  match c with
  | some c' => if isAlphaNum c' then fail s!"expected word boundary after '{kw}'"
  | none => pure ()

private def reservedKeywords : List String :=
  ["begin", "end", "endcase", "endmodule", "endgenerate", "endtask",
   "if", "else", "case", "casez", "default", "for",
   "module", "input", "output", "inout", "wire", "reg", "integer",
   "assign", "always", "generate", "task", "parameter", "localparam",
   "posedge", "negedge", "or"]

def identifier : P String := token do
  let savedPos ← getPos
  let first ← nextChar
  if !isAlpha first then fail s!"expected identifier, got '{first}'"
  let mut result : List Char := [first]
  let mut cont := true
  while cont do
    let c ← peekChar
    match c with
    | some c' =>
      if isAlphaNum c' then let _ ← nextChar; result := result ++ [c']
      else cont := false
    | none => cont := false
  let name := String.ofList result
  if reservedKeywords.any (· == name) then
    setPos savedPos
    fail s!"'{name}' is a reserved keyword, expected identifier"
  pure name

-- ============================================================================
-- Numeric literals
-- ============================================================================

def digits : P String := do
  let first ← nextChar
  if !isDigit first then fail s!"expected digit, got '{first}'"
  let mut result : List Char := [first]
  let mut cont := true
  while cont do
    let c ← peekChar
    match c with
    | some c' =>
      if isDigit c' then let _ ← nextChar; result := result ++ [c']
      else cont := false
    | none => cont := false
  pure (String.ofList result)

def hexDigitsStr : P String := do
  let first ← nextChar
  if !isHexDigit first then fail s!"expected hex digit, got '{first}'"
  let mut result : List Char := [first]
  let mut cont := true
  while cont do
    let c ← peekChar
    match c with
    | some c' =>
      if isHexDigit c' then let _ ← nextChar; result := result ++ [c']
      else cont := false
    | none => cont := false
  pure (String.ofList result)

def binDigitsStr : P String := do
  let first ← nextChar
  if !isBinDigit first then fail s!"expected binary digit, got '{first}'"
  let mut result : List Char := [first]
  let mut cont := true
  while cont do
    let c ← peekChar
    match c with
    | some c' =>
      if isBinDigit c' then let _ ← nextChar; result := result ++ [c']
      else cont := false
    | none => cont := false
  pure (String.ofList result)

def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
             else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
             else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
             else 0
    acc * 16 + d) 0

def binToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 2 + if c == '1' then 1 else 0) 0  -- x/z → 0

def skipUnderscoresAndSpaces : P Unit := do
  let mut cont := true
  while cont do
    let c ← peekChar
    if c == some '_' || c == some ' ' then let _ ← nextChar
    else cont := false

def hexDigitsWithUnderscore : P String := do
  skipUnderscoresAndSpaces
  let first ← nextChar
  if !isHexDigit first then fail s!"expected hex digit, got '{first}'"
  let mut result : List Char := [first]
  let mut cont := true
  while cont do
    let c ← peekChar
    match c with
    | some c' =>
      if isHexDigit c' then let _ ← nextChar; result := result ++ [c']
      else if c' == '_' then let _ ← nextChar  -- skip underscores
      else cont := false
    | none => cont := false
  pure (String.ofList result)

def numericLiteral : P SVLiteral := token do
  let d ← digits
  let next ← peekChar
  if next == some '\'' then
    let _ ← nextChar
    let base ← nextChar
    match base with
    | 'h' | 'H' =>
      let hd ← hexDigitsWithUnderscore
      pure (SVLiteral.hex (some d.toNat!) (hexToNat hd))
    | 'd' | 'D' =>
      skipUnderscoresAndSpaces
      let dd ← digits
      pure (SVLiteral.decimal (some d.toNat!) dd.toNat!)
    | 'b' | 'B' =>
      skipUnderscoresAndSpaces
      let bd ← binDigitsStr
      pure (SVLiteral.binary (some d.toNat!) (binToNat bd))
    | _ => fail s!"unknown base '{base}'"
  else
    pure (SVLiteral.decimal none d.toNat!)

-- ============================================================================
-- Punctuation
-- ============================================================================

def semi     : P Unit := token (matchStr ";")
def comma    : P Unit := token (matchStr ",")
def lparen   : P Unit := token (matchStr "(")
def rparen   : P Unit := token (matchStr ")")
def lbracket : P Unit := token (matchStr "[")
def rbracket : P Unit := token (matchStr "]")
def lbrace   : P Unit := token (matchStr "{")
def rbrace   : P Unit := token (matchStr "}")
def colon    : P Unit := token (matchStr ":")
def dot      : P Unit := token (matchStr ".")
def at_      : P Unit := token (matchStr "@")
def eqSign   : P Unit := token (matchStr "=")
def qmark    : P Unit := token (matchStr "?")
def op2 (s : String) : P Unit := token (matchStr s)

/-- Parse a bit range [hi:lo]. For parameterized widths like [N-1:0],
    skip over identifiers and treat as [31:0] (default 32-bit). -/
def bitRange : P (Nat × Nat) := do
  lbracket
  let hi ← parseBitRangeVal
  colon
  let lo ← parseBitRangeVal
  rbracket
  pure (hi, lo)
where
  parseBitRangeVal : P Nat := do
    let c ← peekChar
    if c.map isDigit == some true then
      let d ← token digits
      -- Check for ±offset
      match ← attempt (token (matchStr "-")) with
      | some _ =>
        let sub ← token digits
        pure (d.toNat! - sub.toNat!)
      | none =>
        match ← attempt (token (matchStr "+")) with
        | some _ => let add ← token digits; pure (d.toNat! + add.toNat!)
        | none => pure d.toNat!
    else
      -- Identifier-based expression (e.g., regindex_bits-1)
      -- Skip until : or ]
      let mut depth : Nat := 0
      let mut result : Nat := 31  -- default
      let mut running := true
      while running do
        let ch ← peekChar
        match ch with
        | some ':' => if depth == 0 then running := false else let _ ← nextChar
        | some ']' => if depth == 0 then running := false else let _ ← nextChar
        | some '[' => let _ ← nextChar; depth := depth + 1
        | some _ => let _ ← nextChar
        | none => running := false
      ws
      pure result

-- ============================================================================
-- Repetition helpers
-- ============================================================================

partial def many (p : P α) : P (Array α) := do
  let mut result : Array α := #[]
  let mut cont := true
  while cont do
    match ← attempt p with
    | some v => result := result.push v
    | none => cont := false
  pure result

def many1 (p : P α) : P (Array α) := do
  let first ← p
  let rest ← many p
  pure (#[first] ++ rest)

-- ============================================================================
-- Run a parser
-- ============================================================================

def run (p : P α) (input : String) : Except String α :=
  let initState : PState := { chars := input.toList.toArray, pos := 0 }
  match (ExceptT.run p).run initState with
  | (.ok a, _) => .ok a
  | (.error e, _) => .error e

end Tools.SVParser.Lexer
