import FastProofTheory.ProofSystems.Rules
import FastProofTheory.Linear.Profile

namespace FastProofTheory.Linear.Syntax

open Rules

inductive Token where
  | ident (text : String)
  | lparen
  | rparen
  | bang
  | tensor
  | with
  | andTok
  | plus
  | orTok
  | lolli
  | imp
  | one
  | top
  | zero
  | bottom
deriving Inhabited, Repr

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_'

private def consumeIdent (chars : List Char) : String × List Char :=
  let rec loop (remaining : List Char) (acc : List Char) :=
    match remaining with
    | c :: rest =>
        if isIdentChar c then
          loop rest (c :: acc)
        else
          (String.ofList acc.reverse, remaining)
    | [] => (String.ofList acc.reverse, [])
  loop chars []

partial def tokenizeChars : List Char → Except String (List Token)
  | [] => .ok []
  | c :: rest =>
      if c.isWhitespace then
        tokenizeChars rest
      else if isIdentChar c then
        let (ident, remaining) := consumeIdent (c :: rest)
        let token :=
          match ident with
          | "one" => Token.one
          | "top" => Token.top
          | "zero" => Token.zero
          | "bot" => Token.bottom
          | "tensor" => Token.tensor
          | "with" => Token.with
          | "and" => Token.andTok
          | "plus" => Token.plus
          | "or" => Token.orTok
          | "lolli" => Token.lolli
          | "imp" => Token.imp
          | _ => Token.ident ident
        match tokenizeChars remaining with
        | .ok tail => .ok (token :: tail)
        | .error err => .error err
      else
        match c, rest with
        | '(', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.lparen :: tail)
            | .error err => .error err
        | ')', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.rparen :: tail)
            | .error err => .error err
        | '!', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.bang :: tail)
            | .error err => .error err
        | '&', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.with :: tail)
            | .error err => .error err
        | '∧', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.andTok :: tail)
            | .error err => .error err
        | '*', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.tensor :: tail)
            | .error err => .error err
        | '+', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.plus :: tail)
            | .error err => .error err
        | '∨', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.orTok :: tail)
            | .error err => .error err
        | '1', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.one :: tail)
            | .error err => .error err
        | '0', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.zero :: tail)
            | .error err => .error err
        | '⊗', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.tensor :: tail)
            | .error err => .error err
        | '⊕', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.plus :: tail)
            | .error err => .error err
        | '⊸', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.lolli :: tail)
            | .error err => .error err
        | '→', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.imp :: tail)
            | .error err => .error err
        | '⟶', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.imp :: tail)
            | .error err => .error err
        | '⊤', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.top :: tail)
            | .error err => .error err
        | '⊥', _ =>
            match tokenizeChars rest with
            | .ok tail => .ok (Token.bottom :: tail)
            | .error err => .error err
        | '-', '>' :: tail =>
            match tokenizeChars tail with
            | .ok tail' => .ok (Token.imp :: tail')
            | .error err => .error err
        | '\\', '/' :: tail =>
            match tokenizeChars tail with
            | .ok tail' => .ok (Token.andTok :: tail')
            | .error err => .error err
        | '/', '\\' :: tail =>
            match tokenizeChars tail with
            | .ok tail' => .ok (Token.orTok :: tail')
            | .error err => .error err
        | _, _ => .error s!"Unexpected character `{c}` in formula."

def tokenize (text : String) : Except String (List Token) :=
  tokenizeChars text.toList

abbrev Parser := List Token → Except String (Formula × List Token)

mutual
  partial def parseArrow : Parser := fun tokens => do
    let (lhs, rest) <- parseAndLike tokens
    match rest with
    | Token.lolli :: tail =>
        let (rhs, final) <- parseArrow tail
        pure (.lolli lhs rhs, final)
    | Token.imp :: tail =>
        let (rhs, final) <- parseArrow tail
        pure (.imp lhs rhs, final)
    | _ => pure (lhs, rest)

  partial def parseAndLike : Parser := fun tokens => do
    let (first, rest) <- parseOrLike tokens
    parseAndLikeTail first rest

  partial def parseAndLikeTail (acc : Formula) : Parser := fun tokens =>
    match tokens with
    | Token.with :: tail => do
        let (rhs, rest) <- parseOrLike tail
        parseAndLikeTail (.with acc rhs) rest
    | Token.andTok :: tail => do
        let (rhs, rest) <- parseOrLike tail
        parseAndLikeTail (.and acc rhs) rest
    | _ => pure (acc, tokens)

  partial def parseOrLike : Parser := fun tokens => do
    let (first, rest) <- parseTensor tokens
    parseOrLikeTail first rest

  partial def parseOrLikeTail (acc : Formula) : Parser := fun tokens =>
    match tokens with
    | Token.plus :: tail => do
        let (rhs, rest) <- parseTensor tail
        parseOrLikeTail (.plus acc rhs) rest
    | Token.orTok :: tail => do
        let (rhs, rest) <- parseTensor tail
        parseOrLikeTail (.or acc rhs) rest
    | _ => pure (acc, tokens)

  partial def parseTensor : Parser := fun tokens => do
    let (first, rest) <- parseUnary tokens
    parseTensorTail first rest

  partial def parseTensorTail (acc : Formula) : Parser := fun tokens =>
    match tokens with
    | Token.tensor :: tail => do
        let (rhs, rest) <- parseUnary tail
        parseTensorTail (.tensor acc rhs) rest
    | _ => pure (acc, tokens)

  partial def parseUnary : Parser := fun tokens =>
    match tokens with
    | Token.bang :: tail => do
        let (inner, rest) <- parseUnary tail
        pure (.bang inner, rest)
    | _ => parsePrimary tokens

  partial def parsePrimary : Parser := fun tokens =>
    match tokens with
    | Token.ident name :: tail => pure (.atom name, tail)
    | Token.one :: tail => pure (.one, tail)
    | Token.top :: tail => pure (.top, tail)
    | Token.zero :: tail => pure (.zero, tail)
    | Token.bottom :: tail => pure (.bottom, tail)
    | Token.lparen :: tail => do
        let (inner, rest) <- parseArrow tail
        match rest with
        | Token.rparen :: final => pure (inner, final)
        | _ => .error "Expected `)`."
    | _ => .error "Expected a linear formula."
end

def parseFormula (text : String) : Except String Formula := do
  let tokens <- tokenize text
  let (formula, rest) <- parseArrow tokens
  match rest with
  | [] => pure formula
  | _ => .error "Unexpected trailing tokens in formula."

private def takeBalanced (openCh closeCh : Char) (chars : List Char) :
    Except String (String × List Char) :=
  let rec loop (depth : Nat) (remaining acc : List Char) :=
    match remaining with
    | [] => .error s!"Expected closing `{closeCh}`."
    | c :: rest =>
        if c = openCh then
          loop (depth + 1) rest (c :: acc)
        else if c = closeCh then
          if depth = 0 then
            .ok (String.ofList acc.reverse, rest)
          else
            loop (depth - 1) rest (c :: acc)
        else
          loop depth rest (c :: acc)
  match chars with
  | c :: rest =>
      if c = openCh then
        loop 0 rest []
      else
        .error s!"Expected `{openCh}`."
  | [] => .error s!"Expected `{openCh}`."

private def trimChars (chars : List Char) : List Char :=
  let left := chars.dropWhile Char.isWhitespace
  (left.reverse.dropWhile Char.isWhitespace).reverse

private def trimString (text : String) : String :=
  String.ofList (trimChars text.toList)

private def parseEquivalentTail (text : String) : Except String Formula := do
  let chars := trimString text |>.toList
  let (lhsText, afterLhs) <- takeBalanced '(' ')' chars
  let afterLhsTrimmed := trimChars afterLhs
  let (rhsText, afterRhs) <- takeBalanced '(' ')' afterLhsTrimmed
  let trailing := trimString (String.ofList afterRhs)
  unless trailing.isEmpty do
    throw s!"Unexpected trailing text after Equivalent statement: `{trailing}`."
  let lhs <- parseFormula lhsText
  let rhs <- parseFormula rhsText
  pure (.with (.lolli lhs rhs) (.lolli rhs lhs))

partial def containsBang : Formula → Bool
  | .bang _ => true
  | .tensor a b => containsBang a || containsBang b
  | .with a b => containsBang a || containsBang b
  | .plus a b => containsBang a || containsBang b
  | .lolli a b => containsBang a || containsBang b
  | .par a b => containsBang a || containsBang b
  | .imp a b => containsBang a || containsBang b
  | .and a b => containsBang a || containsBang b
  | .or a b => containsBang a || containsBang b
  | .all _ a => containsBang a
  | .ex _ a => containsBang a
  | .whyNot a => containsBang a
  | _ => false

partial def containsLinearConnective : Formula → Bool
  | .tensor a b => containsLinearConnective a || containsLinearConnective b || true
  | .with a b => containsLinearConnective a || containsLinearConnective b || true
  | .plus a b => containsLinearConnective a || containsLinearConnective b || true
  | .lolli a b => containsLinearConnective a || containsLinearConnective b || true
  | .par a b => containsLinearConnective a || containsLinearConnective b || true
  | .bang a => containsLinearConnective a || true
  | .whyNot a => containsLinearConnective a || true
  | .one => true
  | .zero => true
  | .top => true
  | .bottom => true
  | .imp a b => containsLinearConnective a || containsLinearConnective b
  | .and a b => containsLinearConnective a || containsLinearConnective b
  | .or a b => containsLinearConnective a || containsLinearConnective b
  | .all _ a => containsLinearConnective a
  | .ex _ a => containsLinearConnective a
  | _ => false

def inferProfileForFormula (formula : Formula) : FastProofTheory.Linear.Profile :=
  if containsBang formula then
    .withExponentials
  else if containsLinearConnective formula then
    .withoutExponentials
  else
    .ipcND

def parseTheoremStatement (text : String) : Except String Formula := do
  let trimmed := trimString text
  if trimmed.startsWith "Equivalent" then
    parseEquivalentTail (trimString (String.ofList (trimmed.toList.drop "Equivalent".length)))
  else
    parseFormula trimmed

partial def renderFormula : Formula → String
  | .atom name => name
  | .tensor a b => s!"({renderFormula a} ⊗ {renderFormula b})"
  | .with a b => s!"({renderFormula a} & {renderFormula b})"
  | .plus a b => s!"({renderFormula a} ⊕ {renderFormula b})"
  | .lolli a b => s!"({renderFormula a} ⊸ {renderFormula b})"
  | .bang a => s!"!{renderFormula a}"
  | .one => "1"
  | .top => "⊤"
  | .zero => "0"
  | .bottom => "⊥"
  | .par a b => s!"({renderFormula a} ⅋ {renderFormula b})"
  | .imp a b => s!"({renderFormula a} ⟶ {renderFormula b})"
  | .and a b => s!"({renderFormula a} ∧ {renderFormula b})"
  | .or a b => s!"({renderFormula a} ∨ {renderFormula b})"
  | .bot => "⊥"
  | .all x a => s!"∀{x}. {renderFormula a}"
  | .ex x a => s!"∃{x}. {renderFormula a}"
  | .pred p _ => p
  | .whyNot a => s!"?{renderFormula a}"

end FastProofTheory.Linear.Syntax
