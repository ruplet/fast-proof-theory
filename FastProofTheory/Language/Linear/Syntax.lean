import FastProofTheory.Rules
import FastProofTheory.DeclaredSystem

namespace FastProofTheory.Linear.Syntax

open Rules

inductive SurfaceFormula where
  | atom (name : Rules.Label)
  | tensor (left right : SurfaceFormula)
  | with (left right : SurfaceFormula)
  | plus (left right : SurfaceFormula)
  | lolli (left right : SurfaceFormula)
  | bang (body : SurfaceFormula)
  | one
  | top
  | zero
  | bottom
  | imp (left right : SurfaceFormula)
  | and (left right : SurfaceFormula)
  | or (left right : SurfaceFormula)
deriving Inhabited, Repr

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

abbrev Parser := List Token → Except String (SurfaceFormula × List Token)

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

  partial def parseAndLikeTail (acc : SurfaceFormula) : Parser := fun tokens =>
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

  partial def parseOrLikeTail (acc : SurfaceFormula) : Parser := fun tokens =>
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

  partial def parseTensorTail (acc : SurfaceFormula) : Parser := fun tokens =>
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
    | _ => .error "Expected a formula."
end

def parseSurfaceFormula (text : String) : Except String SurfaceFormula := do
  let tokens <- tokenize text
  let (formula, rest) <- parseArrow tokens
  match rest with
  | [] => pure formula
  | _ => .error "Unexpected trailing tokens in formula."

mutual
  private def termEq : Rules.Term → Rules.Term → Bool
    | .var x, .var y => x = y
    | .fn f xs, .fn g ys => f = g && listTermEq xs ys
    | _, _ => false

  private def listTermEq : List Rules.Term → List Rules.Term → Bool
    | [], [] => true
    | x :: xs, y :: ys => termEq x y && listTermEq xs ys
    | _, _ => false
end

partial def formulaEq : Formula → Formula → Bool
  | .atom a, .atom b => a = b
  | .pred p xs, .pred q ys => p = q && listTermEq xs ys
  | .imp a₁ b₁, .imp a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .and a₁ b₁, .and a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .or a₁ b₁, .or a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .bot, .bot => true
  | .all x a, .all y b => x = y && formulaEq a b
  | .ex x a, .ex y b => x = y && formulaEq a b
  | .tensor a₁ b₁, .tensor a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .par a₁ b₁, .par a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .with a₁ b₁, .with a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .plus a₁ b₁, .plus a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .lolli a₁ b₁, .lolli a₂ b₂ => formulaEq a₁ a₂ && formulaEq b₁ b₂
  | .bang a, .bang b => formulaEq a b
  | .whyNot a, .whyNot b => formulaEq a b
  | .one, .one => true
  | .zero, .zero => true
  | .top, .top => true
  | .bottom, .bottom => true
  | _, _ => false

private def connectiveNotAllowed {α} (system : DeclaredSystem) (name : String) : Except String α :=
  .error s!"Connective `{name}` is not available in {system.displayName}."

partial def elaborateFormula (system : DeclaredSystem) : SurfaceFormula → Except String Formula
  | .atom name => pure (.atom name)
  | .tensor a b =>
      if system.isLinearGentzen then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.tensor left right)
      else connectiveNotAllowed system "⊗"
  | .with a b =>
      if system.isLinearGentzen then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.with left right)
      else if system.isNaturalDeduction && (system.isNJp || system.isNKp) then
          connectiveNotAllowed system "& (use ∧ in ND profiles)"
      else connectiveNotAllowed system "&"
  | .plus a b =>
      if system.isLinearGentzen then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.plus left right)
      else connectiveNotAllowed system "⊕"
  | .lolli a b =>
      if system.isLinearGentzen then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.lolli left right)
      else connectiveNotAllowed system "⊸"
  | .bang a =>
      match system with
      | .gentzen (.linearLogic .llBang) =>
          do
            let body <- elaborateFormula system a
            pure (.bang body)
      | _ =>
          connectiveNotAllowed system "!"
  | .one =>
      if system.isLinearGentzen then pure .one else connectiveNotAllowed system "1"
  | .top =>
      if system.isLinearGentzen then pure .top else connectiveNotAllowed system "⊤"
  | .zero =>
      if system.isLinearGentzen then pure .zero else connectiveNotAllowed system "0"
  | .bottom =>
      if system.isLinearGentzen then
        pure .bottom
      else if system.isNaturalDeduction && (system.isNJp || system.isNKp) then
        pure .bot
      else
        connectiveNotAllowed system "⊥"
  | .imp a b =>
      if system.isNaturalDeduction && (system.isNJp || system.isNKp || system.isSystemF) then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.imp left right)
      else connectiveNotAllowed system "→"
  | .and a b =>
      if system.isNaturalDeduction && (system.isNJp || system.isNKp) then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.and left right)
      else connectiveNotAllowed system "∧"
  | .or a b =>
      if system.isNaturalDeduction && (system.isNJp || system.isNKp) then
          do
            let left <- elaborateFormula system a
            let right <- elaborateFormula system b
            pure (.or left right)
      else connectiveNotAllowed system "∨"

def parseFormula (system : DeclaredSystem) (text : String) : Except String Formula := do
  let surface <- parseSurfaceFormula text
  let formula <- elaborateFormula system surface
  unless system.allowsFormula formula do
    throw s!"Formula is not in the language of {system.displayName}."
  pure formula

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

private def parseEquivalentTail (system : DeclaredSystem) (text : String) : Except String Formula := do
  let chars := trimString text |>.toList
  let (lhsText, afterLhs) <- takeBalanced '(' ')' chars
  let afterLhsTrimmed := trimChars afterLhs
  let (rhsText, afterRhs) <- takeBalanced '(' ')' afterLhsTrimmed
  let trailing := trimString (String.ofList afterRhs)
  unless trailing.isEmpty do
    throw s!"Unexpected trailing text after Equivalent statement: `{trailing}`."
  let lhs <- parseFormula system lhsText
  let rhs <- parseFormula system rhsText
  pure (.with (.lolli lhs rhs) (.lolli rhs lhs))

def parseTheoremStatement (system : DeclaredSystem) (text : String) : Except String Formula := do
  let trimmed := trimString text
  if trimmed.startsWith "Equivalent" then
    parseEquivalentTail system (trimString (String.ofList (trimmed.toList.drop "Equivalent".length)))
  else
    parseFormula system trimmed

partial def renderFormula : Formula → String
  | .atom name => toString name
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
  | .pred p _ => toString p
  | .whyNot a => s!"?{renderFormula a}"

end FastProofTheory.Linear.Syntax
