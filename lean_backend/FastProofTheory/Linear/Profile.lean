namespace FastProofTheory.Linear

inductive RuleKind where
  | assumption
  | useUnrestricted
  | withLeft1
  | withLeft2
  | tensorLeft
  | plusLeftElim
  | lolliLeft
  | bangLeft
  | tensorIntro
  | withIntro
  | plusLeft
  | plusRight
  | lolliIntro
  | bangIntro
  | oneIntro
  | topIntro
deriving BEq, DecidableEq, Inhabited, Repr

inductive Logic where
  | ll
  | ipc
  | cpc
deriving BEq, DecidableEq, Inhabited, Repr

inductive Calculus where
  | gentzen
  | nd
deriving BEq, DecidableEq, Inhabited, Repr

structure Profile where
  logic : Logic
  calculus : Calculus
  exponentials : Bool := false
deriving BEq, DecidableEq, Inhabited, Repr

def Profile.withoutExponentials : Profile :=
  { logic := .ll, calculus := .gentzen, exponentials := false }

def Profile.withExponentials : Profile :=
  { logic := .ll, calculus := .gentzen, exponentials := true }

def Profile.ipcND : Profile :=
  { logic := .ipc, calculus := .nd, exponentials := false }

def Profile.cpcND : Profile :=
  { logic := .cpc, calculus := .nd, exponentials := false }

def Profile.allowsExponentials (profile : Profile) : Bool :=
  profile.logic = .ll && profile.exponentials

def Profile.isLinearGentzen (profile : Profile) : Bool :=
  profile.logic = .ll && profile.calculus = .gentzen

def Profile.isNaturalDeduction (profile : Profile) : Bool :=
  profile.calculus = .nd

def Profile.allowsRule (profile : Profile) (rule : RuleKind) : Bool :=
  match rule with
  | .bangIntro => profile.allowsExponentials
  | .bangLeft => profile.allowsExponentials
  | _ => true

def Profile.displayName (profile : Profile) : String :=
  match profile.logic with
  | .ll =>
      if profile.exponentials then "LL!" else "LL"
  | .ipc => "IPC"
  | .cpc => "CPC"

def Profile.calculusName (profile : Profile) : String :=
  match profile.calculus with
  | .gentzen => "Sequent Calculus"
  | .nd => "Natural Deduction"

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
  | "IPC" :: "IN" :: "ND" :: [] => some .ipcND
  | "IPC" :: "ND" :: [] => some .ipcND
  | "CPC" :: "IN" :: "ND" :: [] => some .cpcND
  | "CPC" :: "ND" :: [] => some .cpcND
  | _ => none

def parseProfileTokens (tokens : List String) : Profile :=
  match parseSupportedProfileTokens? tokens with
  | some profile => profile
  | none => .withoutExponentials

end FastProofTheory.Linear
