import Logic.Rules

namespace FastProofTheory.Gentzen.Rules.Linear

open Rules

abbrev Formula := Rules.Formula

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

def RuleKind.displayName : RuleKind → String
  | .assumption => "assumption"
  | .useUnrestricted => "useUnrestricted"
  | .withLeft1 => "withLeft1"
  | .withLeft2 => "withLeft2"
  | .tensorLeft => "tensorLeft"
  | .plusLeftElim => "plusLeftElim"
  | .lolliLeft => "lolliLeft"
  | .bangLeft => "bangLeft"
  | .tensorIntro => "tensorIntro"
  | .withIntro => "withIntro"
  | .plusLeft => "plusLeft"
  | .plusRight => "plusRight"
  | .lolliIntro => "lolliIntro"
  | .bangIntro => "bangIntro"
  | .oneIntro => "oneIntro"
  | .topIntro => "topIntro"
end FastProofTheory.Gentzen.Rules.Linear
