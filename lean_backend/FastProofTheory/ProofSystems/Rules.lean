namespace Rules

inductive Term where
| var : String -> Term
| fn : String -> List Term -> Term

inductive Formula where
| atom : String -> Formula
| pred : String -> List Term -> Formula
| imp : Formula -> Formula -> Formula
| and : Formula -> Formula -> Formula
| or : Formula -> Formula -> Formula
| bot : Formula
| all : String -> Formula -> Formula
| ex : String -> Formula -> Formula
| tensor : Formula -> Formula -> Formula
| par : Formula -> Formula -> Formula
| with : Formula -> Formula -> Formula
| plus : Formula -> Formula -> Formula
| lolli : Formula -> Formula -> Formula
| bang : Formula -> Formula
| whyNot : Formula -> Formula
| one : Formula
| zero : Formula
| top : Formula
| bottom : Formula

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

def neg (A : Formula) : Formula := A ⟶ ⊥
scoped prefix:max "¬" => neg

def substTerm (x : String) (t : Term) : Term -> Term
| .var y => if x = y then t else .var y
| .fn f args => .fn f (args.map (substTerm x t))

def substFormula (x : String) (t : Term) : Formula -> Formula
| .atom p => .atom p
| .pred p args => .pred p (args.map (substTerm x t))
| .imp A B => .imp (substFormula x t A) (substFormula x t B)
| .and A B => .and (substFormula x t A) (substFormula x t B)
| .or A B => .or (substFormula x t A) (substFormula x t B)
| .bot => .bot
| .all y A => if x = y then .all y A else .all y (substFormula x t A)
| .ex y A => if x = y then .ex y A else .ex y (substFormula x t A)
| .tensor A B => .tensor (substFormula x t A) (substFormula x t B)
| .par A B => .par (substFormula x t A) (substFormula x t B)
| .with A B => .with (substFormula x t A) (substFormula x t B)
| .plus A B => .plus (substFormula x t A) (substFormula x t B)
| .lolli A B => .lolli (substFormula x t A) (substFormula x t B)
| .bang A => .bang (substFormula x t A)
| .whyNot A => .whyNot (substFormula x t A)
| .one => .one
| .zero => .zero
| .top => .top
| .bottom => .bottom

def isImplicational : Formula -> Prop
| .atom _ => True
| .pred _ _ => True
| .imp A B => isImplicational A /\ isImplicational B
| _ => False

abbrev Context := List Formula
abbrev Antecedent := List Formula
abbrev Succedent := List Formula
abbrev SingleSuccedent := Option Formula
abbrev Unrestricted := List Formula
abbrev LinearContext := List Formula

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
| forallIntro {Γ : Context} {x : String} {A : Formula} :
    NDProof System Γ A ->
    NDProof System Γ (.all x A)
| forallElim {Γ : Context} {x : String} {A : Formula} {t : Term} :
    NDProof System Γ (.all x A) ->
    NDProof System Γ (substFormula x t A)
| existsIntro {Γ : Context} {x : String} {A : Formula} {t : Term} :
    NDProof System Γ (substFormula x t A) ->
    NDProof System Γ (.ex x A)
| existsElim {Γ : Context} {x y : String} {A B : Formula} :
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
| forallLeft {Γ : Antecedent} {Δ : Succedent} {x : String} {A : Formula} {t : Term} :
    SequentProof System ((substFormula x t A) :: Γ) Δ ->
    SequentProof System ((.all x A) :: Γ) Δ
| existsLeft {Γ : Antecedent} {Δ : Succedent} {x y : String} {A : Formula} :
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
| forallRight {Γ : Antecedent} {Δ : Succedent} {x y : String} {A : Formula} :
    SequentProof System Γ ((substFormula x (.var y) A) :: Δ) ->
    SequentProof System Γ ((.all x A) :: Δ)
| existsRight {Γ : Antecedent} {Δ : Succedent} {x : String} {A : Formula} {t : Term} :
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
| forallLeft {Γ : Antecedent} {C : Formula} {x : String} {A : Formula} {t : Term} :
    IntuitionisticSequentProof System ((substFormula x t A) :: Γ) (.some C) ->
    IntuitionisticSequentProof System ((.all x A) :: Γ) (.some C)
| existsLeft {Γ : Antecedent} {C : Formula} {x y : String} {A : Formula} :
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
| forallRight {Γ : Antecedent} {x y : String} {A : Formula} :
    IntuitionisticSequentProof System Γ (.some (substFormula x (.var y) A)) ->
    IntuitionisticSequentProof System Γ (.some (.all x A))
| existsRight {Γ : Antecedent} {x : String} {A : Formula} {t : Term} :
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
