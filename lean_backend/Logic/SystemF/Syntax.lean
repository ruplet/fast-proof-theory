namespace Logic.SystemF

inductive Ty where
  | var : String → Ty
  | arr : Ty → Ty → Ty
  | all : String → Ty → Ty
deriving Inhabited, Repr

inductive Tm where
  | var : String → Tm
  | lam : String → Ty → Tm → Tm
  | app : Tm → Tm → Tm
  | tyLam : String → Tm → Tm
  | tyApp : Tm → Ty → Tm
deriving Inhabited, Repr

abbrev Context := List (String × Ty)

private def eraseDupStrings : List String → List String
  | [] => []
  | x :: xs =>
      let rest := eraseDupStrings xs
      if x ∈ rest then rest else x :: rest

def Ty.freeVars : Ty → List String
  | .var x => [x]
  | .arr a b => eraseDupStrings (a.freeVars ++ b.freeVars)
  | .all x body => body.freeVars.erase x

def Context.freeTyVars (ctx : Context) : List String :=
  let rec collect : Context → List String
    | [] => []
    | (_, ty) :: rest => ty.freeVars ++ collect rest
  eraseDupStrings (collect ctx)

def Ty.occursFree (x : String) (ty : Ty) : Bool :=
  x ∈ ty.freeVars

partial def Ty.eq : Ty → Ty → Bool
  | .var x, .var y => x = y
  | .arr a₁ b₁, .arr a₂ b₂ => Ty.eq a₁ a₂ && Ty.eq b₁ b₂
  | .all x a, .all y b => x = y && Ty.eq a b
  | _, _ => false

def Context.lookup? : Context → String → Option Ty
  | [], _ => none
  | (name, ty) :: rest, x =>
      if name = x then some ty else Context.lookup? rest x

partial def Ty.subst? (x : String) (replacement : Ty) : Ty → Except String Ty
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

partial def Tm.substTy? (x : String) (replacement : Ty) : Tm → Except String Tm
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

end Logic.SystemF
