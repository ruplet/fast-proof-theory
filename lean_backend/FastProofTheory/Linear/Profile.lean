namespace FastProofTheory.Linear

inductive RuleKind where
  | assumption
  | useUnrestricted
  | tensorIntro
  | withIntro
  | plusLeft
  | plusRight
  | lolliIntro
  | bangIntro
  | oneIntro
  | topIntro
deriving BEq, DecidableEq, Inhabited, Repr

inductive Fragment where
  | multiplicativeAdditive
  | withExponentials
deriving BEq, DecidableEq, Inhabited, Repr

structure Profile where
  fragment : Fragment
deriving BEq, DecidableEq, Inhabited, Repr

def Profile.withoutExponentials : Profile :=
  { fragment := .multiplicativeAdditive }

def Profile.withExponentials : Profile :=
  { fragment := .withExponentials }

def Profile.allowsExponentials (profile : Profile) : Bool :=
  match profile.fragment with
  | .multiplicativeAdditive => false
  | .withExponentials => true

def Profile.allowsRule (profile : Profile) (rule : RuleKind) : Bool :=
  match rule with
  | .bangIntro => profile.allowsExponentials
  | _ => true

def Profile.displayName (profile : Profile) : String :=
  match profile.fragment with
  | .multiplicativeAdditive => "LL"
  | .withExponentials => "LL!"

def parseProfileTokens (tokens : List String) : Profile :=
  match tokens.map String.toUpper with
  | "LL" :: "IN" :: "GENTZEN" :: [] => .withoutExponentials
  | "LL" :: "EXP" :: "IN" :: "GENTZEN" :: [] => .withExponentials
  | "LL" :: "BANG" :: "IN" :: "GENTZEN" :: [] => .withExponentials
  | "LL!" :: "IN" :: "GENTZEN" :: [] => .withExponentials
  | "LL" :: "EXP" :: [] => .withExponentials
  | "LL" :: "BANG" :: [] => .withExponentials
  | "LL!" :: [] => .withExponentials
  | "LL" :: [] => .withoutExponentials
  | _ => .withoutExponentials

def parseSupportedProfileTokens? (tokens : List String) : Option Profile :=
  match tokens.map String.toUpper with
  | "LL" :: [] => some .withoutExponentials
  | "LL" :: "IN" :: "GENTZEN" :: [] => some .withoutExponentials
  | "LL!" :: [] => some .withExponentials
  | "LL!" :: "IN" :: "GENTZEN" :: [] => some .withExponentials
  | "LL" :: "EXP" :: [] => some .withExponentials
  | "LL" :: "BANG" :: [] => some .withExponentials
  | "LL" :: "EXP" :: "IN" :: "GENTZEN" :: [] => some .withExponentials
  | "LL" :: "BANG" :: "IN" :: "GENTZEN" :: [] => some .withExponentials
  | _ => none

end FastProofTheory.Linear
