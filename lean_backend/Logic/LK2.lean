import Logic.Rules

namespace Logic.LK2

open Rules

/-!
LK2 deep embedding. The syntax and proof shape follow LogicalFoundations2010,
Defs. IV.2.1-IV.2.4 and IV.4.1-IV.4.4.
-/

structure Signature where
  NumFn : Type
  StrFn : Type
  Pred : Type
  numFnArity : NumFn → Nat × Nat
  strFnArity : StrFn → Nat × Nat
  predArity : Pred → Nat × Nat

mutual
  inductive NTerm (σ : Signature) where
    | var : String → NTerm σ
    | fn : σ.NumFn → List (NTerm σ) -> List (STerm σ) -> NTerm σ
  deriving Inhabited

  inductive STerm (σ : Signature) where
    | var : String → STerm σ
    | fn : σ.StrFn → List (NTerm σ) -> List (STerm σ) -> STerm σ
  deriving Inhabited
end

mutual
  inductive Formula (σ : Signature) where
    | top : Formula σ
    | bot : Formula σ
    | pred : σ.Pred → List (NTerm σ) → List (STerm σ) → Formula σ
    | eqN : NTerm σ → NTerm σ → Formula σ
    | eqS : STerm σ → STerm σ → Formula σ
    | neg : Formula σ → Formula σ
    | imp : Formula σ → Formula σ → Formula σ
    | and : Formula σ → Formula σ → Formula σ
    | or : Formula σ → Formula σ → Formula σ
    | forallN : String → Formula σ → Formula σ
    | existsN : String → Formula σ → Formula σ
    | forallS : String → Formula σ → Formula σ
    | existsS : String → Formula σ → Formula σ
  deriving Inhabited
end

scoped notation "⊤₂" => Formula.top
scoped notation "⊥₂" => Formula.bot
scoped prefix:max "¬₂" => Formula.neg
scoped infixr:60 " ⟶₂ " => Formula.imp
scoped infixr:55 " ∧₂ " => Formula.and
scoped infixr:50 " ∨₂ " => Formula.or

private def eraseDupStrings : List String → List String := List.eraseDups

private def freshVar (base : String) (avoid : List String) : String :=
  let rec apostrophes : Nat → String
    | 0 => ""
    | n + 1 => apostrophes n ++ "'"
  let candidates := (List.range (avoid.length + 1)).map (fun n => base ++ apostrophes n)
  match candidates.filter (fun c => c ∉ avoid) with
  | c :: _ => c
  | [] => base

mutual
  partial def NTerm.freeNVars : NTerm σ → List String
    | .var x => [x]
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeNVars ++ ss.flatMap STerm.freeNVars)

  partial def NTerm.freeSVars : NTerm σ → List String
    | .var _ => []
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeSVars ++ ss.flatMap STerm.freeSVars)

  partial def STerm.freeNVars : STerm σ → List String
    | .var _ => []
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeNVars ++ ss.flatMap STerm.freeNVars)

  partial def STerm.freeSVars : STerm σ → List String
    | .var x => [x]
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeSVars ++ ss.flatMap STerm.freeSVars)

  partial def NTerm.allNames : NTerm σ → List String
    | .var x => [x]
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.allNames ++ ss.flatMap STerm.allNames)

  partial def STerm.allNames : STerm σ → List String
    | .var x => [x]
    | .fn _ ns ss => eraseDupStrings (ns.flatMap NTerm.allNames ++ ss.flatMap STerm.allNames)
end

mutual
  partial def Formula.freeNVars : Formula σ → List String
    | .top => []
    | .bot => []
    | .pred _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeNVars ++ ss.flatMap STerm.freeNVars)
    | .eqN t u => eraseDupStrings (t.freeNVars ++ u.freeNVars)
    | .eqS t u => eraseDupStrings (t.freeNVars ++ u.freeNVars)
    | .neg A => A.freeNVars
    | .imp A B => eraseDupStrings (A.freeNVars ++ B.freeNVars)
    | .and A B => eraseDupStrings (A.freeNVars ++ B.freeNVars)
    | .or A B => eraseDupStrings (A.freeNVars ++ B.freeNVars)
    | .forallN x A => (A.freeNVars).erase x
    | .existsN x A => (A.freeNVars).erase x
    | .forallS _ A => A.freeNVars
    | .existsS _ A => A.freeNVars

  partial def Formula.freeSVars : Formula σ → List String
    | .top => []
    | .bot => []
    | .pred _ ns ss => eraseDupStrings (ns.flatMap NTerm.freeSVars ++ ss.flatMap STerm.freeSVars)
    | .eqN t u => eraseDupStrings (t.freeSVars ++ u.freeSVars)
    | .eqS t u => eraseDupStrings (t.freeSVars ++ u.freeSVars)
    | .neg A => A.freeSVars
    | .imp A B => eraseDupStrings (A.freeSVars ++ B.freeSVars)
    | .and A B => eraseDupStrings (A.freeSVars ++ B.freeSVars)
    | .or A B => eraseDupStrings (A.freeSVars ++ B.freeSVars)
    | .forallN _ A => A.freeSVars
    | .existsN _ A => A.freeSVars
    | .forallS x A => (A.freeSVars).erase x
    | .existsS x A => (A.freeSVars).erase x

  partial def Formula.allNames : Formula σ → List String
    | .top => []
    | .bot => []
    | .pred _ ns ss => eraseDupStrings (ns.flatMap NTerm.allNames ++ ss.flatMap STerm.allNames)
    | .eqN t u => eraseDupStrings (t.allNames ++ u.allNames)
    | .eqS t u => eraseDupStrings (t.allNames ++ u.allNames)
    | .neg A => A.allNames
    | .imp A B => eraseDupStrings (A.allNames ++ B.allNames)
    | .and A B => eraseDupStrings (A.allNames ++ B.allNames)
    | .or A B => eraseDupStrings (A.allNames ++ B.allNames)
    | .forallN x A => (x :: A.allNames).eraseDups
    | .existsN x A => (x :: A.allNames).eraseDups
    | .forallS x A => (x :: A.allNames).eraseDups
    | .existsS x A => (x :: A.allNames).eraseDups
end

mutual
  partial def NTerm.renameNVar (old new : String) : NTerm σ → NTerm σ
    | .var y => if y = old then .var new else .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.renameNVar old new)) (ss.map (STerm.renameNVar old new))

  partial def NTerm.renameSVar (old new : String) : NTerm σ → NTerm σ
    | .var y => .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.renameSVar old new)) (ss.map (STerm.renameSVar old new))

  partial def STerm.renameNVar (old new : String) : STerm σ → STerm σ
    | .var y => .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.renameNVar old new)) (ss.map (STerm.renameNVar old new))

  partial def STerm.renameSVar (old new : String) : STerm σ → STerm σ
    | .var y => if y = old then .var new else .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.renameSVar old new)) (ss.map (STerm.renameSVar old new))
end

mutual
  partial def Formula.renameNVar (old new : String) : Formula σ → Formula σ
    | .top => .top
    | .bot => .bot
    | .pred p ns ss => .pred p (ns.map (NTerm.renameNVar old new)) (ss.map (STerm.renameNVar old new))
    | .eqN t u => .eqN (NTerm.renameNVar old new t) (NTerm.renameNVar old new u)
    | .eqS t u => .eqS (STerm.renameNVar old new t) (STerm.renameNVar old new u)
    | .neg A => .neg (Formula.renameNVar old new A)
    | .imp A B => .imp (Formula.renameNVar old new A) (Formula.renameNVar old new B)
    | .and A B => .and (Formula.renameNVar old new A) (Formula.renameNVar old new B)
    | .or A B => .or (Formula.renameNVar old new A) (Formula.renameNVar old new B)
    | .forallN x A =>
        if x = old then .forallN x A else .forallN x (Formula.renameNVar old new A)
    | .existsN x A =>
        if x = old then .existsN x A else .existsN x (Formula.renameNVar old new A)
    | .forallS x A => .forallS x (Formula.renameNVar old new A)
    | .existsS x A => .existsS x (Formula.renameNVar old new A)

  partial def Formula.renameSVar (old new : String) : Formula σ → Formula σ
    | .top => .top
    | .bot => .bot
    | .pred p ns ss => .pred p (ns.map (NTerm.renameSVar old new)) (ss.map (STerm.renameSVar old new))
    | .eqN t u => .eqN (NTerm.renameSVar old new t) (NTerm.renameSVar old new u)
    | .eqS t u => .eqS (STerm.renameSVar old new t) (STerm.renameSVar old new u)
    | .neg A => .neg (Formula.renameSVar old new A)
    | .imp A B => .imp (Formula.renameSVar old new A) (Formula.renameSVar old new B)
    | .and A B => .and (Formula.renameSVar old new A) (Formula.renameSVar old new B)
    | .or A B => .or (Formula.renameSVar old new A) (Formula.renameSVar old new B)
    | .forallN x A => .forallN x (Formula.renameSVar old new A)
    | .existsN x A => .existsN x (Formula.renameSVar old new A)
    | .forallS x A =>
        if x = old then .forallS x A else .forallS x (Formula.renameSVar old new A)
    | .existsS x A =>
        if x = old then .existsS x A else .existsS x (Formula.renameSVar old new A)
end

mutual
  partial def NTerm.substN (x : String) (t : NTerm σ) : NTerm σ → NTerm σ
    | .var y => if x = y then t else .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.substN x t)) (ss.map (STerm.substN x t))

  partial def STerm.substN (x : String) (t : NTerm σ) : STerm σ → STerm σ
    | .var y => .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.substN x t)) (ss.map (STerm.substN x t))

  partial def NTerm.substS (x : String) (t : STerm σ) : NTerm σ → NTerm σ
    | .var y => .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.substS x t)) (ss.map (STerm.substS x t))

  partial def STerm.substS (x : String) (t : STerm σ) : STerm σ → STerm σ
    | .var y => if x = y then t else .var y
    | .fn f ns ss => .fn f (ns.map (NTerm.substS x t)) (ss.map (STerm.substS x t))
end

mutual
  partial def Formula.substN (x : String) (t : NTerm σ) : Formula σ → Formula σ
    | .top => .top
    | .bot => .bot
    | .pred p ns ss => .pred p (ns.map (NTerm.substN x t)) (ss.map (STerm.substN x t))
    | .eqN a b => .eqN (NTerm.substN x t a) (NTerm.substN x t b)
    | .eqS a b => .eqS (STerm.substN x t a) (STerm.substN x t b)
    | .neg A => .neg (Formula.substN x t A)
    | .imp A B => .imp (Formula.substN x t A) (Formula.substN x t B)
    | .and A B => .and (Formula.substN x t A) (Formula.substN x t B)
    | .or A B => .or (Formula.substN x t A) (Formula.substN x t B)
    | .forallN y A =>
        if x = y then
          .forallN y A
        else
          if y ∈ t.freeNVars then
            let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
            let fresh := freshVar y avoid
            let renamed := A.renameNVar y fresh
            .forallN fresh (Formula.substN x t renamed)
          else
            .forallN y (Formula.substN x t A)
      | .existsN y A =>
        if x = y then
          .existsN y A
        else
          if y ∈ t.freeNVars then
            let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
            let fresh := freshVar y avoid
            let renamed := A.renameNVar y fresh
            .existsN fresh (Formula.substN x t renamed)
          else
            .existsN y (Formula.substN x t A)
    | .forallS y A =>
        if y ∈ t.freeSVars then
          let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := A.renameSVar y fresh
          .forallS fresh (Formula.substN x t renamed)
        else
          .forallS y (Formula.substN x t A)
    | .existsS y A =>
        if y ∈ t.freeSVars then
          let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := A.renameSVar y fresh
          .existsS fresh (Formula.substN x t renamed)
        else
          .existsS y (Formula.substN x t A)

  partial def Formula.substS (x : String) (t : STerm σ) : Formula σ → Formula σ
    | .top => .top
    | .bot => .bot
    | .pred p ns ss => .pred p (ns.map (NTerm.substS x t)) (ss.map (STerm.substS x t))
    | .eqN a b => .eqN (NTerm.substS x t a) (NTerm.substS x t b)
    | .eqS a b => .eqS (STerm.substS x t a) (STerm.substS x t b)
    | .neg A => .neg (Formula.substS x t A)
    | .imp A B => .imp (Formula.substS x t A) (Formula.substS x t B)
    | .and A B => .and (Formula.substS x t A) (Formula.substS x t B)
    | .or A B => .or (Formula.substS x t A) (Formula.substS x t B)
    | .forallN y A =>
        if y ∈ t.freeNVars then
          let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := A.renameNVar y fresh
          .forallN fresh (Formula.substS x t renamed)
        else
          .forallN y (Formula.substS x t A)
    | .existsN y A =>
        if y ∈ t.freeNVars then
          let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
          let fresh := freshVar y avoid
          let renamed := A.renameNVar y fresh
          .existsN fresh (Formula.substS x t renamed)
        else
          .existsN y (Formula.substS x t A)
    | .forallS y A =>
        if x = y then
          .forallS y A
        else
          if y ∈ t.freeSVars then
            let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
            let fresh := freshVar y avoid
            let renamed := A.renameSVar y fresh
            .forallS fresh (Formula.substS x t renamed)
          else
            .forallS y (Formula.substS x t A)
    | .existsS y A =>
        if x = y then
          .existsS y A
        else
          if y ∈ t.freeSVars then
            let avoid := (t.allNames ++ A.allNames ++ [x, y]).eraseDups
            let fresh := freshVar y avoid
            let renamed := A.renameSVar y fresh
            .existsS fresh (Formula.substS x t renamed)
          else
            .existsS y (Formula.substS x t A)
end

abbrev Antecedent (σ : Signature) := List (Formula σ)
abbrev Succedent (σ : Signature) := List (Formula σ)

def Antecedent.freeNVars {σ : Signature} (Γ : Antecedent σ) : List String :=
  (Γ.map Formula.freeNVars).flatten.eraseDups

def Antecedent.freeSVars {σ : Signature} (Γ : Antecedent σ) : List String :=
  (Γ.map Formula.freeSVars).flatten.eraseDups

def Succedent.freeNVars {σ : Signature} (Δ : Succedent σ) : List String :=
  (Δ.map Formula.freeNVars).flatten.eraseDups

def Succedent.freeSVars {σ : Signature} (Δ : Succedent σ) : List String :=
  (Δ.map Formula.freeSVars).flatten.eraseDups

mutual
  def NTerm.wellFormed : NTerm σ → Prop
    | .var _ => True
    | .fn f ns ss =>
        And (ns.length = (σ.numFnArity f).1)
          (And (ss.length = (σ.numFnArity f).2)
            (And (∀ t ∈ ns, NTerm.wellFormed t) (∀ t ∈ ss, STerm.wellFormed t)))

  def STerm.wellFormed : STerm σ → Prop
    | .var _ => True
    | .fn f ns ss =>
        And (ns.length = (σ.strFnArity f).1)
          (And (ss.length = (σ.strFnArity f).2)
            (And (∀ t ∈ ns, NTerm.wellFormed t) (∀ t ∈ ss, STerm.wellFormed t)))

  def Formula.wellFormed : Formula σ → Prop
    | .top => True
    | .bot => True
    | .pred p ns ss =>
        And (ns.length = (σ.predArity p).1)
          (And (ss.length = (σ.predArity p).2)
            (And (∀ t ∈ ns, NTerm.wellFormed t) (∀ t ∈ ss, STerm.wellFormed t)))
    | .eqN t u => And (NTerm.wellFormed t) (NTerm.wellFormed u)
    | .eqS t u => And (STerm.wellFormed t) (STerm.wellFormed u)
    | .neg A => Formula.wellFormed A
    | .imp A B => And (Formula.wellFormed A) (Formula.wellFormed B)
    | .and A B => And (Formula.wellFormed A) (Formula.wellFormed B)
    | .or A B => And (Formula.wellFormed A) (Formula.wellFormed B)
    | .forallN _ A => Formula.wellFormed A
    | .existsN _ A => Formula.wellFormed A
    | .forallS _ A => Formula.wellFormed A
    | .existsS _ A => Formula.wellFormed A
end

def mkNumFn? {σ : Signature} (f : σ.NumFn) (ns : List (NTerm σ)) (ss : List (STerm σ)) :
    Except String (NTerm σ) := do
  let ar := σ.numFnArity f
  if _h : And (ns.length = ar.1) (ss.length = ar.2) then
    pure (.fn f ns ss)
  else
    throw s!"Number function arity mismatch: expected ({ar.1}, {ar.2})."

def mkStrFn? {σ : Signature} (f : σ.StrFn) (ns : List (NTerm σ)) (ss : List (STerm σ)) :
    Except String (STerm σ) := do
  let ar := σ.strFnArity f
  if _h : And (ns.length = ar.1) (ss.length = ar.2) then
    pure (.fn f ns ss)
  else
    throw s!"String function arity mismatch: expected ({ar.1}, {ar.2})."

def mkPred? {σ : Signature} (p : σ.Pred) (ns : List (NTerm σ)) (ss : List (STerm σ)) :
    Except String (Formula σ) := do
  let ar := σ.predArity p
  if _h : And (ns.length = ar.1) (ss.length = ar.2) then
    pure (.pred p ns ss)
  else
    throw s!"Predicate arity mismatch: expected ({ar.1}, {ar.2})."

inductive EqualityAxiom (σ : Signature) where
  | numRefl : NTerm σ → EqualityAxiom σ
  | numSymm : NTerm σ → NTerm σ → EqualityAxiom σ
  | numTrans : NTerm σ → NTerm σ → NTerm σ → EqualityAxiom σ
  | strRefl : STerm σ → EqualityAxiom σ
  | strSymm : STerm σ → STerm σ → EqualityAxiom σ
  | strTrans : STerm σ → STerm σ → STerm σ → EqualityAxiom σ
  | numFnCongr : (f : σ.NumFn) → List (NTerm σ × NTerm σ) → List (STerm σ × STerm σ) → EqualityAxiom σ
  | strFnCongr : (f : σ.StrFn) → List (NTerm σ × NTerm σ) → List (STerm σ × STerm σ) → EqualityAxiom σ
  | predCongr : (p : σ.Pred) → List (NTerm σ × NTerm σ) → List (STerm σ × STerm σ) → EqualityAxiom σ
deriving Inhabited

def EqualityAxiom.toSequent {σ : Signature} : EqualityAxiom σ → Antecedent σ × Succedent σ
  | .numRefl t => ([], [.eqN t t])
  | .numSymm t u => ([.eqN t u], [.eqN u t])
  | .numTrans t u v => ([.eqN t u, .eqN u v], [.eqN t v])
  | .strRefl t => ([], [.eqS t t])
  | .strSymm t u => ([.eqS t u], [.eqS u t])
  | .strTrans t u v => ([.eqS t u, .eqS u v], [.eqS t v])
  | .numFnCongr f xs ss =>
      (xs.map (fun p => .eqN p.1 p.2) ++ ss.map (fun p => .eqS p.1 p.2),
       [.eqN (.fn f (xs.map Prod.fst) (ss.map Prod.fst)) (.fn f (xs.map Prod.snd) (ss.map Prod.snd))])
  | .strFnCongr f xs ss =>
      (xs.map (fun p => .eqN p.1 p.2) ++ ss.map (fun p => .eqS p.1 p.2),
       [.eqS (.fn f (xs.map Prod.fst) (ss.map Prod.fst)) (.fn f (xs.map Prod.snd) (ss.map Prod.snd))])
  | .predCongr p xs ss =>
      (xs.map (fun p => .eqN p.1 p.2) ++ ss.map (fun p => .eqS p.1 p.2) ++ [.pred p (xs.map Prod.fst) (ss.map Prod.fst)],
       [.pred p (xs.map Prod.snd) (ss.map Prod.snd)])

inductive NonLogicalAxiom (σ : Signature) where
  | formula : Formula σ → NonLogicalAxiom σ
  | equality : EqualityAxiom σ → NonLogicalAxiom σ
deriving Inhabited

def NonLogicalAxiom.toSequent {σ : Signature} : NonLogicalAxiom σ → Antecedent σ × Succedent σ
  | .formula A => ([], [A])
  | .equality ax => ax.toSequent

/-!
Definition IV.4.4: LK2 proofs with cut and the full structural/congruence rule
set, plus the anchoredness notion.

This is raw LK2 syntax. Arity and eigenvariable side conditions are tracked in
the constructors and helpers, but proofs are not normalized into a separate
well-formed proof object yet.
-/
inductive Proof (σ : Signature) : Antecedent σ → Succedent σ → Type where
  | axiom {Γ Δ : Antecedent σ} {A : Formula σ} :
      Proof σ (A :: Γ) (A :: Δ)
  | nonLogicalAxiom (ax : NonLogicalAxiom σ) :
      Proof σ ax.toSequent.1 ax.toSequent.2
  | cut {Γ Γ' : Antecedent σ} {Δ Δ' : Succedent σ} {A : Formula σ} :
      Proof σ Γ (A :: Δ) →
      Proof σ (A :: Γ') Δ' →
      Proof σ (Γ ++ Γ') (Δ ++ Δ')
  | andLeft₁ {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ (A :: Γ) Δ →
      Proof σ ((A ∧₂ B) :: Γ) Δ
  | andLeft₂ {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ (B :: Γ) Δ →
      Proof σ ((A ∧₂ B) :: Γ) Δ
  | orLeft {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ (A :: Γ) Δ →
      Proof σ (B :: Γ) Δ →
      Proof σ ((A ∨₂ B) :: Γ) Δ
  | impLeft {Γ Γ' : Antecedent σ} {Δ Δ' : Succedent σ} {A B : Formula σ} :
      Proof σ Γ (A :: Δ) →
      Proof σ (B :: Γ') Δ' →
      Proof σ ((A ⟶₂ B) :: (Γ ++ Γ')) (Δ ++ Δ')
  | negLeft {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ Γ (A :: Δ) →
      Proof σ ((¬₂ A) :: Γ) Δ
  | forallNLeft {Γ : Antecedent σ} {Δ : Succedent σ} {x : String} {A : Formula σ} {t : NTerm σ} :
      Proof σ ((Formula.substN x t A) :: Γ) Δ →
      Proof σ ((.forallN x A) :: Γ) Δ
  | existsNLeft {Γ : Antecedent σ} {Δ : Succedent σ} {x y : String} {A : Formula σ}
      (hy : y ∉ (Γ.freeNVars ++ Δ.freeNVars ++ Formula.freeNVars (.existsN x A))) :
      Proof σ ((Formula.substN x (.var y) A) :: Γ) Δ →
      Proof σ ((.existsN x A) :: Γ) Δ
  | forallSLeft {Γ : Antecedent σ} {Δ : Succedent σ} {x : String} {A : Formula σ} {t : STerm σ} :
      Proof σ ((Formula.substS x t A) :: Γ) Δ →
      Proof σ ((.forallS x A) :: Γ) Δ
  | existsSLeft {Γ : Antecedent σ} {Δ : Succedent σ} {x y : String} {A : Formula σ}
      (hy : y ∉ (Γ.freeSVars ++ Δ.freeSVars ++ Formula.freeSVars (.existsS x A))) :
      Proof σ ((Formula.substS x (.var y) A) :: Γ) Δ →
      Proof σ ((.existsS x A) :: Γ) Δ
  | botLeft {Γ : Antecedent σ} {Δ : Succedent σ} :
      Proof σ (.bot :: Γ) Δ
  | andRight {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ Γ (A :: Δ) →
      Proof σ Γ (B :: Δ) →
      Proof σ Γ ((A ∧₂ B) :: Δ)
  | orRight₁ {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ Γ (A :: Δ) →
      Proof σ Γ ((A ∨₂ B) :: Δ)
  | orRight₂ {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ Γ (B :: Δ) →
      Proof σ Γ ((A ∨₂ B) :: Δ)
  | impRight {Γ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ (A :: Γ) (B :: Δ) →
      Proof σ Γ ((A ⟶₂ B) :: Δ)
  | negRight {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ (A :: Γ) Δ →
      Proof σ Γ ((¬₂ A) :: Δ)
  | forallNRight {Γ : Antecedent σ} {Δ : Succedent σ} {x y : String} {A : Formula σ}
      (hy : y ∉ (Γ.freeNVars ++ Δ.freeNVars ++ Formula.freeNVars (.forallN x A))) :
      Proof σ Γ ((Formula.substN x (.var y) A) :: Δ) →
      Proof σ Γ ((.forallN x A) :: Δ)
  | existsNRight {Γ : Antecedent σ} {Δ : Succedent σ} {x : String} {A : Formula σ} {t : NTerm σ} :
      Proof σ Γ ((Formula.substN x t A) :: Δ) →
      Proof σ Γ ((.existsN x A) :: Δ)
  | forallSRight {Γ : Antecedent σ} {Δ : Succedent σ} {x : String} {A : Formula σ} {y : String}
      (hy : y ∉ (Γ.freeSVars ++ Δ.freeSVars ++ Formula.freeSVars (.forallS x A))) :
      Proof σ Γ ((Formula.substS x (.var y) A) :: Δ) →
      Proof σ Γ ((.forallS x A) :: Δ)
  | existsSRight {Γ : Antecedent σ} {Δ : Succedent σ} {x : String} {A : Formula σ} {t : STerm σ} :
      Proof σ Γ ((Formula.substS x t A) :: Δ) →
      Proof σ Γ ((.existsS x A) :: Δ)
  | leftWeakening {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ Γ Δ →
      Proof σ (A :: Γ) Δ
  | rightWeakening {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ Γ Δ →
      Proof σ Γ (A :: Δ)
  | leftContraction {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ (A :: A :: Γ) Δ →
      Proof σ (A :: Γ) Δ
  | rightContraction {Γ : Antecedent σ} {Δ : Succedent σ} {A : Formula σ} :
      Proof σ Γ (A :: A :: Δ) →
      Proof σ Γ (A :: Δ)
  | leftPermutation {Γ₁ Γ₂ : Antecedent σ} {Δ : Succedent σ} {A B : Formula σ} :
      Proof σ (Γ₁ ++ A :: B :: Γ₂) Δ →
      Proof σ (Γ₁ ++ B :: A :: Γ₂) Δ
  | rightPermutation {Γ : Antecedent σ} {Δ₁ Δ₂ : Succedent σ} {A B : Formula σ} :
      Proof σ Γ (Δ₁ ++ A :: B :: Δ₂) →
      Proof σ Γ (Δ₁ ++ B :: A :: Δ₂)

def Proof.cutFormulas {σ : Signature} : {Γ : Antecedent σ} → {Δ : Succedent σ} → Proof σ Γ Δ → List (Formula σ)
  | _, _, .axiom => []
  | _, _, .nonLogicalAxiom _ => []
  | _, _, .cut (A := A) p q => A :: (Proof.cutFormulas p ++ Proof.cutFormulas q)
  | _, _, .andLeft₁ p => Proof.cutFormulas p
  | _, _, .andLeft₂ p => Proof.cutFormulas p
  | _, _, .orLeft p q => Proof.cutFormulas p ++ Proof.cutFormulas q
  | _, _, .impLeft p q => Proof.cutFormulas p ++ Proof.cutFormulas q
  | _, _, .negLeft p => Proof.cutFormulas p
  | _, _, .forallNLeft p => Proof.cutFormulas p
  | _, _, .existsNLeft _ p => Proof.cutFormulas p
  | _, _, .forallSLeft p => Proof.cutFormulas p
  | _, _, .existsSLeft _ p => Proof.cutFormulas p
  | _, _, .botLeft => []
  | _, _, .andRight p q => Proof.cutFormulas p ++ Proof.cutFormulas q
  | _, _, .orRight₁ p => Proof.cutFormulas p
  | _, _, .orRight₂ p => Proof.cutFormulas p
  | _, _, .impRight p => Proof.cutFormulas p
  | _, _, .negRight p => Proof.cutFormulas p
  | _, _, .forallNRight _ p => Proof.cutFormulas p
  | _, _, .existsNRight p => Proof.cutFormulas p
  | _, _, .forallSRight _ p => Proof.cutFormulas p
  | _, _, .existsSRight p => Proof.cutFormulas p
  | _, _, .leftWeakening p => Proof.cutFormulas p
  | _, _, .rightWeakening p => Proof.cutFormulas p
  | _, _, .leftContraction p => Proof.cutFormulas p
  | _, _, .rightContraction p => Proof.cutFormulas p
  | _, _, .leftPermutation p => Proof.cutFormulas p
  | _, _, .rightPermutation p => Proof.cutFormulas p

def Proof.nonLogicalAxiomFormulas {σ : Signature} : {Γ : Antecedent σ} → {Δ : Succedent σ} → Proof σ Γ Δ → List (Formula σ)
  | _, _, .axiom => []
  | _, _, .nonLogicalAxiom ax => ax.toSequent.1 ++ ax.toSequent.2
  | _, _, .cut (A := _) p q => Proof.nonLogicalAxiomFormulas p ++ Proof.nonLogicalAxiomFormulas q
  | _, _, .andLeft₁ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .andLeft₂ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .orLeft p q => Proof.nonLogicalAxiomFormulas p ++ Proof.nonLogicalAxiomFormulas q
  | _, _, .impLeft p q => Proof.nonLogicalAxiomFormulas p ++ Proof.nonLogicalAxiomFormulas q
  | _, _, .negLeft p => Proof.nonLogicalAxiomFormulas p
  | _, _, .forallNLeft p => Proof.nonLogicalAxiomFormulas p
  | _, _, .existsNLeft _ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .forallSLeft p => Proof.nonLogicalAxiomFormulas p
  | _, _, .existsSLeft _ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .botLeft => []
  | _, _, .andRight p q => Proof.nonLogicalAxiomFormulas p ++ Proof.nonLogicalAxiomFormulas q
  | _, _, .orRight₁ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .orRight₂ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .impRight p => Proof.nonLogicalAxiomFormulas p
  | _, _, .negRight p => Proof.nonLogicalAxiomFormulas p
  | _, _, .forallNRight _ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .existsNRight p => Proof.nonLogicalAxiomFormulas p
  | _, _, .forallSRight _ p => Proof.nonLogicalAxiomFormulas p
  | _, _, .existsSRight p => Proof.nonLogicalAxiomFormulas p
  | _, _, .leftWeakening p => Proof.nonLogicalAxiomFormulas p
  | _, _, .rightWeakening p => Proof.nonLogicalAxiomFormulas p
  | _, _, .leftContraction p => Proof.nonLogicalAxiomFormulas p
  | _, _, .rightContraction p => Proof.nonLogicalAxiomFormulas p
  | _, _, .leftPermutation p => Proof.nonLogicalAxiomFormulas p
  | _, _, .rightPermutation p => Proof.nonLogicalAxiomFormulas p

def Proof.IsAnchored {σ : Signature} {Γ : Antecedent σ} {Δ : Succedent σ} (p : Proof σ Γ Δ) : Prop :=
  ∀ A, A ∈ Proof.cutFormulas p → A ∈ Proof.nonLogicalAxiomFormulas p

/-!
Small build-time examples for Definition IV.4.4.
-/
private def exampleSignature : Signature where
  NumFn := Unit
  StrFn := Unit
  Pred := Unit
  numFnArity := fun _ => (0, 0)
  strFnArity := fun _ => (0, 0)
  predArity := fun _ => (0, 0)

private def exampleAtom : Formula exampleSignature := .pred () [] []

private def exampleNonLogical : NonLogicalAxiom exampleSignature := .formula exampleAtom

private def anchoredByNoCuts : Proof exampleSignature [exampleAtom] [exampleAtom] := .axiom

example : Proof.IsAnchored (p := anchoredByNoCuts) := by
  intro A h
  cases h

private def anchoredCutProof : Proof exampleSignature [] [exampleAtom] :=
  .cut (.nonLogicalAxiom exampleNonLogical) .axiom

private theorem anchoredCutNonLogical :
    Proof.nonLogicalAxiomFormulas anchoredCutProof = [exampleAtom] := by
  simp [anchoredCutProof, Proof.nonLogicalAxiomFormulas, exampleNonLogical, NonLogicalAxiom.toSequent]

example : Proof.IsAnchored (p := anchoredCutProof) := by
  intro A h
  simp [anchoredCutProof, Proof.cutFormulas] at h
  cases h
  rw [anchoredCutNonLogical]
  simp

private def notAnchoredProof : Proof exampleSignature [exampleAtom] [exampleAtom] :=
  .cut (Γ := [exampleAtom]) (Γ' := []) (Δ := []) (Δ' := [exampleAtom]) (A := exampleAtom) .axiom .axiom

example : ¬ Proof.IsAnchored (p := notAnchoredProof) := by
  intro h
  have hcut : exampleAtom ∈ Proof.cutFormulas notAnchoredProof := by
    simp [notAnchoredProof, Proof.cutFormulas]
  have hax := h exampleAtom hcut
  simp [notAnchoredProof, Proof.nonLogicalAxiomFormulas] at hax

example : freshVar "y" (["y", "x"] : List String) = "y'" := by
  rfl

/-!
Definition IV.5. The single-sorted interpretation reuses `Rules.Formula` and
the `FS`/`SS` unary predicates.
-/
namespace SingleSorted

structure Names (σ : Signature) where
  numFn : σ.NumFn → String
  strFn : σ.StrFn → String
  pred : σ.Pred → String

def fs (t : Rules.Term) : Rules.Formula := .pred "FS" [t]
def ss (t : Rules.Term) : Rules.Formula := .pred "SS" [t]

def andList : List Rules.Formula → Rules.Formula
  | [] => .top
  | A :: As => As.foldr Rules.Formula.and A

def allMany : List String → Rules.Formula → Rules.Formula
  | [], A => A
  | x :: xs, A => .all x (allMany xs A)

def exMany : List String → Rules.Formula → Rules.Formula
  | [], A => A
  | x :: xs, A => .ex x (exMany xs A)

mutual
  partial def toFOTermN {σ : Signature} (names : Names σ) : NTerm σ → Rules.Term
    | .var x => .var x
    | .fn f ns ss => .fn (names.numFn f) (ns.map (toFOTermN names) ++ ss.map (toFOTermS names))

  partial def toFOTermS {σ : Signature} (names : Names σ) : STerm σ → Rules.Term
    | .var x => .var x
    | .fn f ns ss => .fn (names.strFn f) (ns.map (toFOTermN names) ++ ss.map (toFOTermS names))
end

def toFOFormula {σ : Signature} (names : Names σ) : Formula σ → Rules.Formula
  | .top => .top
  | .bot => .bot
  | .pred p ns ss => .pred (names.pred p) (ns.map (toFOTermN names) ++ ss.map (toFOTermS names))
  | .eqN t u => .pred "=" [toFOTermN names t, toFOTermN names u]
  | .eqS t u => .pred "=" [toFOTermS names t, toFOTermS names u]
  | .neg A => Rules.neg (toFOFormula names A)
  | .imp A B => .imp (toFOFormula names A) (toFOFormula names B)
  | .and A B => .and (toFOFormula names A) (toFOFormula names B)
  | .or A B => .or (toFOFormula names A) (toFOFormula names B)
  | .forallN x A => .all x (.imp (fs (.var x)) (toFOFormula names A))
  | .existsN x A => .ex x (.and (fs (.var x)) (toFOFormula names A))
  | .forallS x A => .all x (.imp (ss (.var x)) (toFOFormula names A))
  | .existsS x A => .ex x (.and (ss (.var x)) (toFOFormula names A))

def phiSortCoverage : Rules.Formula :=
  .all "x" (.or (fs (.var "x")) (ss (.var "x")))

def phiNonemptyFS : Rules.Formula :=
  .ex "x" (fs (.var "x"))

def phiNonemptySS : Rules.Formula :=
  .ex "x" (ss (.var "x"))

private def vars : String → Nat → List String
  | _, 0 => []
  | base, n + 1 => base :: vars (base ++ "'") n

private def argsHaveSorts (numVars strVars : List String) : List Rules.Formula :=
  (numVars.map (fun x => fs (.var x))) ++ (strVars.map (fun x => ss (.var x)))

def phiForNumFn {σ : Signature} (names : Names σ) (f : σ.NumFn) : Rules.Formula :=
  let ar := σ.numFnArity f
  let numVars := vars "n" ar.1
  let strVars := vars "s" ar.2
  let premises := argsHaveSorts numVars strVars
  let conclusion := fs (toFOTermN names (.fn f (numVars.map NTerm.var) (strVars.map STerm.var)))
  allMany (numVars ++ strVars) (Rules.Formula.imp (andList premises) conclusion)

def phiForStrFn {σ : Signature} (names : Names σ) (f : σ.StrFn) : Rules.Formula :=
  let ar := σ.strFnArity f
  let numVars := vars "n" ar.1
  let strVars := vars "s" ar.2
  let premises := argsHaveSorts numVars strVars
  let conclusion := ss (toFOTermS names (.fn f (numVars.map NTerm.var) (strVars.map STerm.var)))
  allMany (numVars ++ strVars) (Rules.Formula.imp (andList premises) conclusion)

def phiForPred {σ : Signature} (names : Names σ) (p : σ.Pred) : Rules.Formula :=
  let ar := σ.predArity p
  let numVars := vars "n" ar.1
  let strVars := vars "s" ar.2
  let premises := [Rules.Formula.pred (names.pred p) (numVars.map (fun x => .var x) ++ strVars.map (fun x => .var x))]
  let concl := andList (argsHaveSorts numVars strVars)
  allMany (numVars ++ strVars) (Rules.Formula.imp (andList premises) concl)

end SingleSorted

end Logic.LK2
