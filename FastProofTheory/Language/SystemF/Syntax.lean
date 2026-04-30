import FastProofTheory.SystemF.Syntax

namespace FastProofTheory.SystemF.Syntax

abbrev Ty := FastProofTheory.SystemF.Ty
abbrev Tm := FastProofTheory.SystemF.Tm
abbrev Label := FastProofTheory.SystemF.Label

private def label (text : String) : Label :=
  ⟨text⟩

inductive Token where
  | ident (text : String)
  | lparen
  | rparen
  | lbrack
  | rbrack
  | colon
  | dot
  | arrow
  | forallTok
  | lambda
  | tyLambda
  | hasType
deriving Inhabited, Repr

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c = '_' || c = '\''

private def consumeIdent (chars : List Char) : String × List Char :=
  let rec loop (remaining acc : List Char) :=
    match remaining with
    | c :: rest =>
        if isIdentChar c then loop rest (c :: acc) else (String.ofList acc.reverse, remaining)
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
          | "forall" => Token.forallTok
          | "all" => Token.forallTok
          | "lambda" => Token.lambda
          | "Lambda" => Token.tyLambda
          | "has_type" => Token.hasType
          | _ => Token.ident ident
        match tokenizeChars remaining with
        | .ok tail => .ok (token :: tail)
        | .error err => .error err
      else
        match c, rest with
        | '(', _ => tokenizeChars rest |>.map (Token.lparen :: ·)
        | ')', _ => tokenizeChars rest |>.map (Token.rparen :: ·)
        | '[', _ => tokenizeChars rest |>.map (Token.lbrack :: ·)
        | ']', _ => tokenizeChars rest |>.map (Token.rbrack :: ·)
        | ':', _ => tokenizeChars rest |>.map (Token.colon :: ·)
        | '.', _ => tokenizeChars rest |>.map (Token.dot :: ·)
        | '→', _ => tokenizeChars rest |>.map (Token.arrow :: ·)
        | '∀', _ => tokenizeChars rest |>.map (Token.forallTok :: ·)
        | 'λ', _ => tokenizeChars rest |>.map (Token.lambda :: ·)
        | 'Λ', _ => tokenizeChars rest |>.map (Token.tyLambda :: ·)
        | '-', '>' :: tail => tokenizeChars tail |>.map (Token.arrow :: ·)
        | '\\', tail => tokenizeChars tail |>.map (Token.lambda :: ·)
        | '/', '\\' :: tail => tokenizeChars tail |>.map (Token.tyLambda :: ·)
        | _, _ => .error s!"Unexpected character `{c}`."

def tokenize (text : String) : Except String (List Token) :=
  tokenizeChars text.toList

abbrev Parser α := List Token → Except String (α × List Token)

structure Judgment where
  term : Tm
  ty : Ty
deriving Inhabited, Repr

mutual
  partial def parseTyArrow : Parser Ty := fun tokens => do
    let (lhs, rest) <- parseTyPrimary tokens
    match rest with
    | Token.arrow :: tail =>
        let (rhs, final) <- parseTyArrow tail
        pure (.arr lhs rhs, final)
    | _ => pure (lhs, rest)

  partial def parseTyPrimary : Parser Ty := fun tokens =>
    match tokens with
    | Token.ident name :: rest => pure (.var (label name), rest)
    | Token.lparen :: rest => do
        let (inner, rest') <- parseTyArrow rest
        match rest' with
        | Token.rparen :: final => pure (inner, final)
        | _ => .error "Expected `)` in type."
    | Token.forallTok :: Token.ident name :: Token.dot :: rest => do
        let (body, final) <- parseTyArrow rest
        pure (.all (label name) body, final)
    | _ => .error "Expected a System F type."
end

private def startsTermAtom : List Token → Bool
  | Token.ident _ :: _ => true
  | Token.lparen :: _ => true
  | Token.lambda :: _ => true
  | Token.tyLambda :: _ => true
  | _ => false

private partial def splitAtHasType : List Token → Except String (List Token × List Token)
  | [] => .error "Expected `has_type` in a System F judgment."
  | Token.hasType :: rest => .ok ([], rest)
  | tok :: rest => do
      let (lhs, rhs) <- splitAtHasType rest
      pure (tok :: lhs, rhs)

mutual
  partial def parseTerm : Parser Tm := parseTermApp

  partial def parseTermApp : Parser Tm := fun tokens => do
    let (first, rest) <- parseTermPostfix tokens
    parseTermAppTail first rest

  partial def parseTermAppTail (acc : Tm) : Parser Tm := fun tokens =>
    if startsTermAtom tokens then do
      let (arg, rest) <- parseTermPostfix tokens
      parseTermAppTail (.app acc arg) rest
    else
      pure (acc, tokens)

  partial def parseTermPostfix : Parser Tm := fun tokens => do
    let (base, rest) <- parseTermPrimary tokens
    parseTermPostfixTail base rest

  partial def parseTermPostfixTail (acc : Tm) : Parser Tm := fun tokens =>
    match tokens with
    | Token.lbrack :: rest => do
        let (ty, rest') <- parseTyArrow rest
        match rest' with
        | Token.rbrack :: final => parseTermPostfixTail (.tyApp acc ty) final
        | _ => .error "Expected `]` after type argument."
    | _ => pure (acc, tokens)

  partial def parseTermPrimary : Parser Tm := fun tokens =>
    match tokens with
    | Token.ident name :: rest => pure (.var (label name), rest)
    | Token.lparen :: rest => do
        let (inner, rest') <- parseTerm rest
        match rest' with
        | Token.rparen :: final => pure (inner, final)
        | _ => .error "Expected `)` in term."
    | Token.lambda :: Token.ident name :: Token.colon :: rest => do
        let (ty, rest') <- parseTyArrow rest
        match rest' with
        | Token.dot :: bodyTokens => do
            let (body, final) <- parseTerm bodyTokens
            pure (.lam (label name) ty body, final)
        | _ => .error "Expected `.` after lambda binder."
    | Token.tyLambda :: Token.ident name :: Token.dot :: rest => do
        let (body, final) <- parseTerm rest
        pure (.tyLam (label name) body, final)
    | _ => .error "Expected a System F term."
end

def parseType (text : String) : Except String Ty := do
  let tokens <- tokenize text
  let (ty, rest) <- parseTyArrow tokens
  match rest with
  | [] => pure ty
  | _ => .error "Unexpected trailing tokens in type."

def parseProofTerm (text : String) : Except String Tm := do
  let tokens <- tokenize text
  let (term, rest) <- parseTerm tokens
  match rest with
  | [] => pure term
  | _ => .error "Unexpected trailing tokens in term."

def parseJudgment (text : String) : Except String Judgment := do
  let tokens <- tokenize text
  let (termTokens, tyTokens) <- splitAtHasType tokens
  if termTokens.isEmpty then
    throw "Expected a System F term before `has_type`."
  let (term, termRest) <- parseTerm termTokens
  match termRest with
  | [] => pure ()
  | _ => .error "Unexpected trailing tokens in System F term."
  let (ty, tyRest) <- parseTyArrow tyTokens
  match tyRest with
  | [] => pure { term, ty }
  | _ => .error "Unexpected trailing tokens in System F judgment."

-- Small parser regressions for the `term has_type type` surface form.
example : (match parseProofTerm "(\\x : p. x)" with | .ok _ => true | .error _ => false) = true := by
  native_decide

example : (match parseJudgment "(\\x : p. x) has_type p -> p" with | .ok _ => true | .error _ => false) = true := by
  native_decide

example : (match parseJudgment "forall p. p -> p" with | .ok _ => true | .error _ => false) = false := by
  native_decide

end FastProofTheory.SystemF.Syntax
