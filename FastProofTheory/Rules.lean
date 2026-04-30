namespace Rules

structure Label where
  text : String
deriving Inhabited, Repr, DecidableEq

instance : ToString Label where
  toString label := label.text

instance : Coe String Label where
  coe text := ⟨text⟩

class FreshLabel (α : Type) where
  next : α → α

instance : FreshLabel Label where
  next label := ⟨label.text ++ "'"⟩

inductive Term (α : Type := Label) where
| var : α -> Term α
| fn : α -> List (Term α) -> Term α
deriving Inhabited, Repr

inductive Formula (α : Type := Label) where
| atom : α -> Formula α
| pred : α -> List (Term α) -> Formula α
| imp : Formula α -> Formula α -> Formula α
| and : Formula α -> Formula α -> Formula α
| or : Formula α -> Formula α -> Formula α
| bot : Formula α
| all : α -> Formula α -> Formula α
| ex : α -> Formula α -> Formula α
| tensor : Formula α -> Formula α -> Formula α
| par : Formula α -> Formula α -> Formula α
| with : Formula α -> Formula α -> Formula α
| plus : Formula α -> Formula α -> Formula α
| lolli : Formula α -> Formula α -> Formula α
| bang : Formula α -> Formula α
| whyNot : Formula α -> Formula α
| one : Formula α
| zero : Formula α
| top : Formula α
| bottom : Formula α
deriving Inhabited, Repr

scoped infixr:60 " ⟶ " => Formula.imp
scoped infixr:55 " ∧ " => Formula.and
scoped infixr:50 " ∨ " => Formula.or
scoped notation "⊥" => Formula.bot

scoped infixr:70 " ⊗ " => Formula.tensor
scoped infixr:65 " ⅋ " => Formula.par
scoped infixr:60 " & " => Formula.with
scoped infixr:55 " ⊕ " => Formula.plus
scoped infixr:50 " ⊸ " => Formula.lolli
scoped notation "⊤ₗ" => Formula.top
scoped notation "⊥ₗ" => Formula.bottom

def neg {α : Type} (A : Formula α) : Formula α := A ⟶ ⊥
scoped prefix:max "¬" => neg

def substTerm [DecidableEq α] (x : α) (t : Term α) : Term α -> Term α
| .var y => if x = y then t else .var y
| .fn f args => .fn f (args.map (substTerm x t))

def Term.freeVars [DecidableEq α] : Term α -> List α
| .var x => [x]
| .fn _ args => args.flatMap Term.freeVars |>.eraseDups

def Term.allNames [DecidableEq α] : Term α -> List α
| .var x => [x]
| .fn _ args => args.flatMap Term.allNames |>.eraseDups

def Formula.freeVars [DecidableEq α] : Formula α -> List α
| .atom _ => []
| .pred _ args => args.flatMap Term.freeVars |>.eraseDups
| .imp A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .and A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .or A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .bot => []
| .all y A => (Formula.freeVars A).erase y
| .ex y A => (Formula.freeVars A).erase y
| .tensor A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .par A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .with A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .plus A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .lolli A B => (Formula.freeVars A ++ Formula.freeVars B).eraseDups
| .bang A => Formula.freeVars A
| .whyNot A => Formula.freeVars A
| .one => []
| .zero => []
| .top => []
| .bottom => []

def Formula.allNames [DecidableEq α] : Formula α -> List α
| .atom name => [name]
| .pred _ args => args.flatMap Term.allNames |>.eraseDups
| .imp A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .and A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .or A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .bot => []
| .all y A => (y :: Formula.allNames A).eraseDups
| .ex y A => (y :: Formula.allNames A).eraseDups
| .tensor A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .par A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .with A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .plus A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .lolli A B => (Formula.allNames A ++ Formula.allNames B).eraseDups
| .bang A => Formula.allNames A
| .whyNot A => Formula.allNames A
| .one => []
| .zero => []
| .top => []
| .bottom => []

private partial def freshVar [DecidableEq α] [FreshLabel α] (base : α) (avoid : List α) : α :=
  let rec loop (candidate : α) : α :=
    if candidate ∈ avoid then loop (FreshLabel.next candidate) else candidate
  loop base

private partial def renameTermVar [DecidableEq α] (old new : α) : Term α -> Term α
| .var y => if y = old then .var new else .var y
| .fn f args => .fn f (args.map (renameTermVar old new))

private partial def renameFormulaVarScoped [DecidableEq α] (old new : α) : Formula α -> Formula α
  | .atom p => .atom p
  | .pred p args => .pred p (args.map (renameTermVar old new))
  | .imp A B => .imp (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .and A B => .and (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .or A B => .or (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .bot => .bot
  | .all y A =>
      if y = old then
        .all y A
      else
        .all y (renameFormulaVarScoped old new A)
  | .ex y A =>
      if y = old then
        .ex y A
      else
        .ex y (renameFormulaVarScoped old new A)
  | .tensor A B => .tensor (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .par A B => .par (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .with A B => .with (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .plus A B => .plus (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .lolli A B => .lolli (renameFormulaVarScoped old new A) (renameFormulaVarScoped old new B)
  | .bang A => .bang (renameFormulaVarScoped old new A)
  | .whyNot A => .whyNot (renameFormulaVarScoped old new A)
  | .one => .one
  | .zero => .zero
  | .top => .top
  | .bottom => .bottom

private partial def substFormulaAvoidCapture [DecidableEq α] [FreshLabel α] (x : α) (t : Term α) : Formula α -> Formula α
  | .atom p => .atom p
  | .pred p args => .pred p (args.map (substTerm x t))
  | .imp A B => .imp (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .and A B => .and (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .or A B => .or (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .bot => .bot
  | .all y A =>
      if x = y then
        .all y A
      else
        let tFVs := Term.freeVars t
        if y ∈ tFVs then
          let avoid := (tFVs ++ Formula.allNames A ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := renameFormulaVarScoped y fresh A
          .all fresh (substFormulaAvoidCapture x t renamed)
        else
          .all y (substFormulaAvoidCapture x t A)
  | .ex y A =>
      if x = y then
        .ex y A
      else
        let tFVs := Term.freeVars t
        if y ∈ tFVs then
          let avoid := (tFVs ++ Formula.allNames A ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := renameFormulaVarScoped y fresh A
          .ex fresh (substFormulaAvoidCapture x t renamed)
        else
          .ex y (substFormulaAvoidCapture x t A)
  | .tensor A B => .tensor (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .par A B => .par (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .with A B => .with (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .plus A B => .plus (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .lolli A B => .lolli (substFormulaAvoidCapture x t A) (substFormulaAvoidCapture x t B)
  | .bang A => .bang (substFormulaAvoidCapture x t A)
  | .whyNot A => .whyNot (substFormulaAvoidCapture x t A)
  | .one => .one
  | .zero => .zero
  | .top => .top
  | .bottom => .bottom

def substFormula [DecidableEq α] [FreshLabel α] (x : α) (t : Term α) : Formula α -> Formula α :=
  substFormulaAvoidCapture x t

def isImplicational {α : Type} : Formula α -> Prop
| .atom _ => True
| .pred _ _ => True
| .imp A B => isImplicational A /\ isImplicational B
| _ => False

abbrev Context (α : Type := Label) := List (Formula α)
abbrev Antecedent (α : Type := Label) := List (Formula α)
abbrev Succedent (α : Type := Label) := List (Formula α)
abbrev SingleSuccedent (α : Type := Label) := Option (Formula α)
abbrev Unrestricted (α : Type := Label) := List (Formula α)
abbrev LinearContext (α : Type := Label) := List (Formula α)

class HasExchange (System : Type) : Prop where
  intro ::

class HasWeakening (System : Type) : Prop where
  intro ::

class HasContraction (System : Type) : Prop where
  intro ::

class HasBottomElim (System : Type) : Prop where
  intro ::

class HasClassicalRule (System : Type) : Prop where
  intro ::

class HasUnrestrictedExchange (System : Type) : Prop where
  intro ::

class HasUnrestrictedWeakening (System : Type) : Prop where
  intro ::

class HasUnrestrictedContraction (System : Type) : Prop where
  intro ::

class HasLinearExchange (System : Type) : Prop where
  intro ::

class HasLeftWeakeningSC (System : Type) : Prop where
  intro ::

class HasRightWeakeningSC (System : Type) : Prop where
  intro ::

class HasLeftContractionSC (System : Type) : Prop where
  intro ::

class HasRightContractionSC (System : Type) : Prop where
  intro ::

class HasLeftPermutationSC (System : Type) : Prop where
  intro ::

class HasRightPermutationSC (System : Type) : Prop where
  intro ::

class HasCutSC (System : Type) : Prop where
  intro ::

inductive NDProof (System : Type) : Context -> Formula -> Type where
| hyp {Γ : Context} {A : Formula} :
    A ∈ Γ ->
    NDProof System Γ A
| exchange [HasExchange System] {Γ₁ Γ₂ : Context} {A B C : Formula} :
    NDProof System (Γ₁ ++ A :: B :: Γ₂) C ->
    NDProof System (Γ₁ ++ B :: A :: Γ₂) C
| weaken [HasWeakening System] {Γ : Context} {A B : Formula} :
    NDProof System Γ A ->
    NDProof System (B :: Γ) A
| contract [HasContraction System] {Γ : Context} {A B : Formula} :
    NDProof System (A :: A :: Γ) B ->
    NDProof System (A :: Γ) B
| impIntro {Γ : Context} {A B : Formula} :
    NDProof System (A :: Γ) B ->
    NDProof System Γ (A ⟶ B)
| impElim {Γ : Context} {A B : Formula} :
    NDProof System Γ (A ⟶ B) ->
    NDProof System Γ A ->
    NDProof System Γ B
| andIntro {Γ : Context} {A B : Formula} :
    NDProof System Γ A ->
    NDProof System Γ B ->
    NDProof System Γ (A ∧ B)
| andLeft {Γ : Context} {A B : Formula} :
    NDProof System Γ (A ∧ B) ->
    NDProof System Γ A
| andRight {Γ : Context} {A B : Formula} :
    NDProof System Γ (A ∧ B) ->
    NDProof System Γ B
| orLeft {Γ : Context} {A B : Formula} :
    NDProof System Γ A ->
    NDProof System Γ (A ∨ B)
| orRight {Γ : Context} {A B : Formula} :
    NDProof System Γ B ->
    NDProof System Γ (A ∨ B)
| orElim {Γ : Context} {A B C : Formula} :
    NDProof System Γ (A ∨ B) ->
    NDProof System (A :: Γ) C ->
    NDProof System (B :: Γ) C ->
    NDProof System Γ C
| bottomElim [HasBottomElim System] {Γ : Context} {A : Formula} :
    NDProof System Γ ⊥ ->
    NDProof System Γ A
| classical [HasClassicalRule System] {Γ : Context} {A : Formula} :
    NDProof System ((¬A) :: Γ) ⊥ ->
    NDProof System Γ A
| forallIntro {Γ : Context} {x : Label} {A : Formula} :
    NDProof System Γ A ->
    NDProof System Γ (.all x A)
| forallElim {Γ : Context} {x : Label} {A : Formula} {t : Term} :
    NDProof System Γ (.all x A) ->
    NDProof System Γ (substFormula x t A)
| existsIntro {Γ : Context} {x : Label} {A : Formula} {t : Term} :
    NDProof System Γ (substFormula x t A) ->
    NDProof System Γ (.ex x A)
| existsElim {Γ : Context} {x y : Label} {A B : Formula} :
    NDProof System Γ (.ex x A) ->
    NDProof System ((substFormula x (.var y) A) :: Γ) B ->
    NDProof System Γ B

inductive LinearNDProof (System : Type) : Unrestricted -> LinearContext -> Formula -> Type where
| hyp {Δ : Unrestricted} {A : Formula} :
    LinearNDProof System Δ [A] A
| unrestricted {Δ : Unrestricted} {A : Formula} :
    A ∈ Δ ->
    LinearNDProof System Δ [] A
| uExchange [HasUnrestrictedExchange System] {Δ₁ Δ₂ : Unrestricted} {Γ : LinearContext}
    {A B C : Formula} :
    LinearNDProof System (Δ₁ ++ A :: B :: Δ₂) Γ C ->
    LinearNDProof System (Δ₁ ++ B :: A :: Δ₂) Γ C
| uWeaken [HasUnrestrictedWeakening System] {Δ : Unrestricted} {Γ : LinearContext}
    {A B : Formula} :
    LinearNDProof System Δ Γ A ->
    LinearNDProof System (B :: Δ) Γ A
| uContract [HasUnrestrictedContraction System] {Δ : Unrestricted} {Γ : LinearContext}
    {A B : Formula} :
    LinearNDProof System (A :: A :: Δ) Γ B ->
    LinearNDProof System (A :: Δ) Γ B
| lExchange [HasLinearExchange System] {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext}
    {A B C : Formula} :
    LinearNDProof System Δ (Γ₁ ++ A :: B :: Γ₂) C ->
    LinearNDProof System Δ (Γ₁ ++ B :: A :: Γ₂) C
| linearImpIntro {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ (A :: Γ) B ->
    LinearNDProof System Δ Γ (A ⊸ B)
| linearImpElim {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ₁ (A ⊸ B) ->
    LinearNDProof System Δ Γ₂ A ->
    LinearNDProof System Δ (Γ₁ ++ Γ₂) B
| tensorIntro {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ₁ A ->
    LinearNDProof System Δ Γ₂ B ->
    LinearNDProof System Δ (Γ₁ ++ Γ₂) (A ⊗ B)
| tensorElim {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext} {A B C : Formula} :
    LinearNDProof System Δ Γ₁ (A ⊗ B) ->
    LinearNDProof System Δ (A :: B :: Γ₂) C ->
    LinearNDProof System Δ (Γ₁ ++ Γ₂) C
| withIntro {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ A ->
    LinearNDProof System Δ Γ B ->
    LinearNDProof System Δ Γ (A & B)
| withLeft {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ (A & B) ->
    LinearNDProof System Δ Γ A
| withRight {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ (A & B) ->
    LinearNDProof System Δ Γ B
| plusLeft {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ A ->
    LinearNDProof System Δ Γ (A ⊕ B)
| plusRight {Δ : Unrestricted} {Γ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ B ->
    LinearNDProof System Δ Γ (A ⊕ B)
| plusElim {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext} {A B C : Formula} :
    LinearNDProof System Δ Γ₁ (A ⊕ B) ->
    LinearNDProof System Δ (A :: Γ₂) C ->
    LinearNDProof System Δ (B :: Γ₂) C ->
    LinearNDProof System Δ (Γ₁ ++ Γ₂) C
| oneIntro {Δ : Unrestricted} :
    LinearNDProof System Δ [] Formula.one
| topIntro {Δ : Unrestricted} {Γ : LinearContext} :
    LinearNDProof System Δ Γ ⊤ₗ
| zeroElim {Δ : Unrestricted} {Γ : LinearContext} {A : Formula} :
    LinearNDProof System Δ Γ Formula.zero ->
    LinearNDProof System Δ Γ A
| bottomElim {Δ : Unrestricted} {Γ : LinearContext} {A : Formula} :
    LinearNDProof System Δ Γ ⊥ₗ ->
    LinearNDProof System Δ Γ A
| bangIntro {Δ : Unrestricted} {A : Formula} :
    LinearNDProof System Δ [] A ->
    LinearNDProof System Δ [] (.bang A)
| bangElim {Δ : Unrestricted} {Γ₁ Γ₂ : LinearContext} {A B : Formula} :
    LinearNDProof System Δ Γ₁ (.bang A) ->
    LinearNDProof System (A :: Δ) Γ₂ B ->
    LinearNDProof System Δ (Γ₁ ++ Γ₂) B

inductive SequentProof (System : Type) : Antecedent -> Succedent -> Type where
| axiom {Γ Δ : Antecedent} {A : Formula} :
    SequentProof System (A :: Γ) (A :: Δ)
| cut [HasCutSC System] {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A : Formula} :
    SequentProof System Γ (A :: Δ) ->
    SequentProof System (A :: Γ') Δ' ->
    SequentProof System (Γ ++ Γ') (Δ ++ Δ')
| andLeft₁ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System (A :: Γ) Δ ->
    SequentProof System ((A ∧ B) :: Γ) Δ
| andLeft₂ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System (B :: Γ) Δ ->
    SequentProof System ((A ∧ B) :: Γ) Δ
| orLeft {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System (A :: Γ) Δ ->
    SequentProof System (B :: Γ) Δ ->
    SequentProof System ((A ∨ B) :: Γ) Δ
| impLeft {Γ Γ' : Antecedent} {Δ Δ' : Succedent} {A B : Formula} :
    SequentProof System Γ (A :: Δ) ->
    SequentProof System (B :: Γ') Δ' ->
    SequentProof System ((A ⟶ B) :: (Γ ++ Γ')) (Δ ++ Δ')
| negLeft {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System Γ (A :: Δ) ->
    SequentProof System ((¬A) :: Γ) Δ
| forallLeft {Γ : Antecedent} {Δ : Succedent} {x : Label} {A : Formula} {t : Term} :
    SequentProof System ((substFormula x t A) :: Γ) Δ ->
    SequentProof System ((.all x A) :: Γ) Δ
| existsLeft {Γ : Antecedent} {Δ : Succedent} {x y : Label} {A : Formula} :
    SequentProof System ((substFormula x (.var y) A) :: Γ) Δ ->
    SequentProof System ((.ex x A) :: Γ) Δ
| botLeft {Γ : Antecedent} {Δ : Succedent} :
    SequentProof System (⊥ :: Γ) Δ
| andRight {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System Γ (A :: Δ) ->
    SequentProof System Γ (B :: Δ) ->
    SequentProof System Γ ((A ∧ B) :: Δ)
| orRight₁ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System Γ (A :: Δ) ->
    SequentProof System Γ ((A ∨ B) :: Δ)
| orRight₂ {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System Γ (B :: Δ) ->
    SequentProof System Γ ((A ∨ B) :: Δ)
| impRight {Γ : Antecedent} {Δ : Succedent} {A B : Formula} :
    SequentProof System (A :: Γ) (B :: Δ) ->
    SequentProof System Γ ((A ⟶ B) :: Δ)
| negRight {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System (A :: Γ) Δ ->
    SequentProof System Γ ((¬A) :: Δ)
| forallRight {Γ : Antecedent} {Δ : Succedent} {x y : Label} {A : Formula} :
    SequentProof System Γ ((substFormula x (.var y) A) :: Δ) ->
    SequentProof System Γ ((.all x A) :: Δ)
| existsRight {Γ : Antecedent} {Δ : Succedent} {x : Label} {A : Formula} {t : Term} :
    SequentProof System Γ ((substFormula x t A) :: Δ) ->
    SequentProof System Γ ((.ex x A) :: Δ)
| leftWeakening [HasLeftWeakeningSC System] {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System Γ Δ ->
    SequentProof System (A :: Γ) Δ
| rightWeakening [HasRightWeakeningSC System] {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System Γ Δ ->
    SequentProof System Γ (A :: Δ)
| leftContraction [HasLeftContractionSC System] {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System (A :: A :: Γ) Δ ->
    SequentProof System (A :: Γ) Δ
| rightContraction [HasRightContractionSC System] {Γ : Antecedent} {Δ : Succedent} {A : Formula} :
    SequentProof System Γ (A :: A :: Δ) ->
    SequentProof System Γ (A :: Δ)
| leftPermutation [HasLeftPermutationSC System] {Γ₁ Γ₂ : Antecedent} {Δ : Succedent}
    {A B : Formula} :
    SequentProof System (Γ₁ ++ A :: B :: Γ₂) Δ ->
    SequentProof System (Γ₁ ++ B :: A :: Γ₂) Δ
| rightPermutation [HasRightPermutationSC System] {Γ : Antecedent} {Δ₁ Δ₂ : Succedent}
    {A B : Formula} :
    SequentProof System Γ (Δ₁ ++ A :: B :: Δ₂) ->
    SequentProof System Γ (Δ₁ ++ B :: A :: Δ₂)

inductive IntuitionisticSequentProof (System : Type) : Antecedent -> SingleSuccedent -> Type where
| axiom {Γ : Antecedent} {A : Formula} :
    IntuitionisticSequentProof System (A :: Γ) (.some A)
| cut [HasCutSC System] {Γ Γ' : Antecedent} {A C : Formula} :
    IntuitionisticSequentProof System Γ (.some A) ->
    IntuitionisticSequentProof System (A :: Γ') (.some C) ->
    IntuitionisticSequentProof System (Γ ++ Γ') (.some C)
| andLeft₁ {Γ : Antecedent} {C A B : Formula} :
    IntuitionisticSequentProof System (A :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((A ∧ B) :: Γ) (.some C)
| andLeft₂ {Γ : Antecedent} {C A B : Formula} :
    IntuitionisticSequentProof System (B :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((A ∧ B) :: Γ) (.some C)
| orLeft {Γ : Antecedent} {C A B : Formula} :
    IntuitionisticSequentProof System (A :: Γ) (.some C) ->
    IntuitionisticSequentProof System (B :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((A ∨ B) :: Γ) (.some C)
| impLeft {Γ Γ' : Antecedent} {A B C : Formula} :
    IntuitionisticSequentProof System Γ (.some A) ->
    IntuitionisticSequentProof System (B :: Γ') (.some C) ->
    IntuitionisticSequentProof System ((A ⟶ B) :: (Γ ++ Γ')) (.some C)
| negLeft {Γ : Antecedent} {A C : Formula} :
    IntuitionisticSequentProof System Γ (.some A) ->
    IntuitionisticSequentProof System ((¬A) :: Γ) (.some C)
| forallLeft {Γ : Antecedent} {C : Formula} {x : Label} {A : Formula} {t : Term} :
    IntuitionisticSequentProof System ((substFormula x t A) :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((.all x A) :: Γ) (.some C)
| existsLeft {Γ : Antecedent} {C : Formula} {x y : Label} {A : Formula} :
    IntuitionisticSequentProof System ((substFormula x (.var y) A) :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((.ex x A) :: Γ) (.some C)
| botLeft {Γ : Antecedent} {C : Formula} :
    IntuitionisticSequentProof System (⊥ :: Γ) (.some C)
| andRight {Γ : Antecedent} {A B : Formula} :
    IntuitionisticSequentProof System Γ (.some A) ->
    IntuitionisticSequentProof System Γ (.some B) ->
    IntuitionisticSequentProof System Γ (.some (A ∧ B))
| orRight₁ {Γ : Antecedent} {A B : Formula} :
    IntuitionisticSequentProof System Γ (.some A) ->
    IntuitionisticSequentProof System Γ (.some (A ∨ B))
| orRight₂ {Γ : Antecedent} {A B : Formula} :
    IntuitionisticSequentProof System Γ (.some B) ->
    IntuitionisticSequentProof System Γ (.some (A ∨ B))
| impRight {Γ : Antecedent} {A B : Formula} :
    IntuitionisticSequentProof System (A :: Γ) (.some B) ->
    IntuitionisticSequentProof System Γ (.some (A ⟶ B))
| negRight {Γ : Antecedent} {A : Formula} :
    IntuitionisticSequentProof System (A :: Γ) none ->
    IntuitionisticSequentProof System Γ (.some (¬A))
| forallRight {Γ : Antecedent} {x y : Label} {A : Formula} :
    IntuitionisticSequentProof System Γ (.some (substFormula x (.var y) A)) ->
    IntuitionisticSequentProof System Γ (.some (.all x A))
| existsRight {Γ : Antecedent} {x : Label} {A : Formula} {t : Term} :
    IntuitionisticSequentProof System Γ (.some (substFormula x t A)) ->
    IntuitionisticSequentProof System Γ (.some (.ex x A))
| leftWeakening [HasLeftWeakeningSC System] {Γ : Antecedent} {C : SingleSuccedent} {A : Formula} :
    IntuitionisticSequentProof System Γ C ->
    IntuitionisticSequentProof System (A :: Γ) C
| leftContraction [HasLeftContractionSC System] {Γ : Antecedent} {C : SingleSuccedent} {A : Formula} :
    IntuitionisticSequentProof System (A :: A :: Γ) C ->
    IntuitionisticSequentProof System (A :: Γ) C
| leftPermutation [HasLeftPermutationSC System] {Γ₁ Γ₂ : Antecedent} {C : SingleSuccedent}
    {A B : Formula} :
    IntuitionisticSequentProof System (Γ₁ ++ A :: B :: Γ₂) C ->
    IntuitionisticSequentProof System (Γ₁ ++ B :: A :: Γ₂) C

end Rules
