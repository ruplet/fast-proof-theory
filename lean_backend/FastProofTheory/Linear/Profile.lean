import Logic.Rules

namespace FastProofTheory.Linear

open Rules

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

inductive RuleSet where
  | ll
  | llBang
  | ipc
  | cpc
  | systemF
deriving BEq, DecidableEq, Inhabited, Repr

inductive Calculus where
  | gentzen
  | nd
deriving BEq, DecidableEq, Inhabited, Repr

inductive Language where
  | ipcImplicational
  | ipcPropositional
  | ipcFull
  | cpcPropositional
  | cpcFull
  | ll
  | llBang
  | systemF
deriving BEq, DecidableEq, Inhabited, Repr

structure Profile where
  rules : RuleSet
  calculus : Calculus
  language : Language
deriving BEq, DecidableEq, Inhabited, Repr

def Profile.withoutExponentials : Profile :=
  { rules := .ll, calculus := .gentzen, language := .ll }

def Profile.withExponentials : Profile :=
  { rules := .llBang, calculus := .gentzen, language := .llBang }

def Profile.ipcNDImplicational : Profile :=
  { rules := .ipc, calculus := .nd, language := .ipcImplicational }

def Profile.ipcNDPropositional : Profile :=
  { rules := .ipc, calculus := .nd, language := .ipcPropositional }

def Profile.ipcNDFull : Profile :=
  { rules := .ipc, calculus := .nd, language := .ipcFull }

def Profile.cpcNDPropositional : Profile :=
  { rules := .cpc, calculus := .nd, language := .cpcPropositional }

def Profile.cpcNDFull : Profile :=
  { rules := .cpc, calculus := .nd, language := .cpcFull }

def Profile.systemFND : Profile :=
  { rules := .systemF, calculus := .nd, language := .systemF }

def Profile.logicName (profile : Profile) : String :=
  match profile.rules with
  | .ll => "LL"
  | .llBang => "LL!"
  | .ipc => "IPC"
  | .cpc => "CPC"
  | .systemF => "SYSTEM_F"

def Profile.calculusName (profile : Profile) : String :=
  match profile.calculus with
  | .gentzen => "GENTZEN"
  | .nd => "ND"

def Language.displayName : Language → String
  | .ipcImplicational => "IPC_IMP"
  | .ipcPropositional => "IPC_PROP"
  | .ipcFull => "IPC_FULL"
  | .cpcPropositional => "CPC_PROP"
  | .cpcFull => "CPC_FULL"
  | .ll => "LL"
  | .llBang => "LL!"
  | .systemF => "SYSTEM_F"

def Profile.languageName (profile : Profile) : String :=
  profile.language.displayName

def Profile.displayName (profile : Profile) : String :=
  s!"{profile.logicName} in {profile.calculusName} with {profile.languageName}"

def Profile.allowsExponentials (profile : Profile) : Bool :=
  profile.rules = .llBang

def Profile.isLinearGentzen (profile : Profile) : Bool :=
  (profile.rules = .ll || profile.rules = .llBang) && profile.calculus = .gentzen

def Profile.isNaturalDeduction (profile : Profile) : Bool :=
  profile.calculus = .nd

def Profile.isIPC (profile : Profile) : Bool :=
  profile.rules = .ipc

def Profile.isCPC (profile : Profile) : Bool :=
  profile.rules = .cpc

def Profile.isSystemF (profile : Profile) : Bool :=
  profile.rules = .systemF

def Profile.hasValidConfiguration (profile : Profile) : Bool :=
  match profile.rules, profile.calculus, profile.language with
  | .ll, .gentzen, .ll => true
  | .llBang, .gentzen, .llBang => true
  | .ipc, .nd, .ipcImplicational => true
  | .ipc, .nd, .ipcPropositional => true
  | .ipc, .nd, .ipcFull => true
  | .cpc, .nd, .cpcPropositional => true
  | .cpc, .nd, .cpcFull => true
  | .systemF, .nd, .systemF => true
  | _, _, _ => false

def Profile.allowsRule (profile : Profile) (rule : RuleKind) : Bool :=
  match rule with
  | .bangIntro => profile.allowsExponentials
  | .bangLeft => profile.allowsExponentials
  | _ => true

partial def Profile.allowsFormula (profile : Profile) : Formula → Bool
  | .atom _ => true
  | .pred _ _ => false
  | .imp a b =>
      match profile.language with
      | .ipcImplicational | .ipcFull | .cpcFull =>
          profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .and a b =>
      match profile.language with
      | .ipcPropositional | .ipcFull | .cpcPropositional | .cpcFull =>
          profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .or a b =>
      match profile.language with
      | .ipcPropositional | .ipcFull | .cpcPropositional | .cpcFull =>
          profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .bot =>
      match profile.language with
      | .ipcImplicational | .ipcPropositional | .ipcFull | .cpcPropositional | .cpcFull => true
      | _ => false
  | .all _ _ => false
  | .ex _ _ => false
  | .tensor a b =>
      match profile.language with
      | .ll | .llBang => profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .par _ _ => false
  | .with a b =>
      match profile.language with
      | .ll | .llBang => profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .plus a b =>
      match profile.language with
      | .ll | .llBang => profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .lolli a b =>
      match profile.language with
      | .ll | .llBang => profile.allowsFormula a && profile.allowsFormula b
      | _ => false
  | .bang a =>
      match profile.language with
      | .llBang => profile.allowsFormula a
      | _ => false
  | .whyNot _ => false
  | .one =>
      match profile.language with
      | .ll | .llBang => true
      | _ => false
  | .zero =>
      match profile.language with
      | .ll | .llBang => true
      | _ => false
  | .top =>
      match profile.language with
      | .ll | .llBang => true
      | _ => false
  | .bottom =>
      match profile.language with
      | .ll | .llBang => true
      | _ => false

def parseSupportedProfileTokens? (tokens : List String) : Option Profile :=
  match tokens.map String.toUpper with
  | "LL" :: "IN" :: "GENTZEN" :: "WITH" :: "LL" :: [] => some .withoutExponentials
  | "LL!" :: "IN" :: "GENTZEN" :: "WITH" :: "LL!" :: [] => some .withExponentials
  | "LL_BANG" :: "IN" :: "GENTZEN" :: "WITH" :: "LL_BANG" :: [] => some .withExponentials
  | "IPC" :: "IN" :: "ND" :: "WITH" :: "IPC_IMP" :: [] => some .ipcNDImplicational
  | "IPC" :: "IN" :: "ND" :: "WITH" :: "IPC_PROP" :: [] => some .ipcNDPropositional
  | "IPC" :: "IN" :: "ND" :: "WITH" :: "IPC_FULL" :: [] => some .ipcNDFull
  | "CPC" :: "IN" :: "ND" :: "WITH" :: "CPC_PROP" :: [] => some .cpcNDPropositional
  | "CPC" :: "IN" :: "ND" :: "WITH" :: "CPC_FULL" :: [] => some .cpcNDFull
  | "SYSTEM_F" :: "IN" :: "ND" :: [] => some .systemFND
  | "SYSTEMF" :: "IN" :: "ND" :: [] => some .systemFND
  | "SYSTEM_F" :: "IN" :: "ND" :: "WITH" :: "SYSTEM_F" :: [] => some .systemFND
  | "SYSTEMF" :: "IN" :: "ND" :: "WITH" :: "SYSTEMF" :: [] => some .systemFND
  | _ => none

def parseProfileTokens (tokens : List String) : Profile :=
  match parseSupportedProfileTokens? tokens with
  | some profile => profile
  | none => .withoutExponentials

end FastProofTheory.Linear
