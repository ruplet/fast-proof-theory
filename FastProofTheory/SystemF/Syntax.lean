import FastProofTheory.Rules

namespace FastProofTheory.SystemF

abbrev Label := Rules.Label

inductive Ty (α : Type := Label) where
  | var : α → Ty α
  | arr : Ty α → Ty α → Ty α
  | all : α → Ty α → Ty α
deriving Inhabited, Repr, DecidableEq

inductive Tm (α : Type := Label) where
  | var : α → Tm α
  | lam : α → Ty α → Tm α → Tm α
  | app : Tm α → Tm α → Tm α
  | tyLam : α → Tm α → Tm α
  | tyApp : Tm α → Ty α → Tm α
deriving Inhabited, Repr, DecidableEq

abbrev Context (α : Type := Label) := List (α × Ty α)

private def eraseDupsLabels [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := eraseDupsLabels xs
      if x ∈ rest then rest else x :: rest

def Ty.freeVars [DecidableEq α] : Ty α → List α
  | .var x => [x]
  | .arr a b => eraseDupsLabels (a.freeVars ++ b.freeVars)
  | .all x body => body.freeVars.erase x

def Context.freeTyVars [DecidableEq α] (ctx : Context α) : List α :=
  let rec collect : Context α → List α
    | [] => []
    | (_, ty) :: rest => ty.freeVars ++ collect rest
  eraseDupsLabels (collect ctx)

def Ty.occursFree [DecidableEq α] (x : α) (ty : Ty α) : Bool :=
  x ∈ ty.freeVars

partial def Ty.eq [DecidableEq α] : Ty α → Ty α → Bool
  | .var x, .var y => x = y
  | .arr a₁ b₁, .arr a₂ b₂ => Ty.eq a₁ a₂ && Ty.eq b₁ b₂
  | .all x a, .all y b => x = y && Ty.eq a b
  | _, _ => false

def Context.lookup? [DecidableEq α] : Context α → α → Option (Ty α)
  | [], _ => none
  | (name, ty) :: rest, x =>
      if name = x then some ty else Context.lookup? rest x

partial def Ty.subst? [DecidableEq α] [ToString α] (x : α) (replacement : Ty α) : Ty α → Except String (Ty α)
  | .var y => pure <| if x = y then replacement else .var y
  | .arr a b => do
      let a' <- Ty.subst? x replacement a
      let b' <- Ty.subst? x replacement b
      pure (.arr a' b')
  | .all y body =>
      if x = y then
        pure (.all y body)
      else if Ty.occursFree y replacement then
        throw s!"Substitution would capture type variable `{y}`."
      else do
        let body' <- Ty.subst? x replacement body
        pure (.all y body')

partial def Tm.substTy? [DecidableEq α] [ToString α] (x : α) (replacement : Ty α) : Tm α → Except String (Tm α)
  | .var y => pure (.var y)
  | .lam y ty body => do
      let ty' <- Ty.subst? x replacement ty
      let body' <- Tm.substTy? x replacement body
      pure (.lam y ty' body')
  | .app fn arg => do
      let fn' <- Tm.substTy? x replacement fn
      let arg' <- Tm.substTy? x replacement arg
      pure (.app fn' arg')
  | .tyLam y body =>
      if x = y then
        pure (.tyLam y body)
      else if Ty.occursFree y replacement then
        throw s!"Substitution would capture type variable `{y}`."
      else do
        let body' <- Tm.substTy? x replacement body
        pure (.tyLam y body')
  | .tyApp fn ty => do
      let fn' <- Tm.substTy? x replacement fn
      let ty' <- Ty.subst? x replacement ty
      pure (.tyApp fn' ty')

end FastProofTheory.SystemF
