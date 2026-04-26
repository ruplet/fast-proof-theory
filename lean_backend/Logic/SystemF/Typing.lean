import Logic.SystemF.Syntax

namespace Logic.SystemF

abbrev TyContext := List String

def TyContext.freeTyVars (Δ : TyContext) : List String :=
  Δ.eraseDups

inductive HasType : TyContext → Context → Tm → Ty → Type where
  | var {Δ Γ x A} :
      Γ.lookup? x = some A →
      HasType Δ Γ (.var x) A
  | lam {Δ Γ x A t B} :
      HasType Δ ((x, A) :: Γ) t B →
      HasType Δ Γ (.lam x A t) (.arr A B)
  | app {Δ Γ f a A B} :
      HasType Δ Γ f (.arr A B) →
      HasType Δ Γ a A →
      HasType Δ Γ (.app f a) B
  | tyLam {Δ Γ X t A} :
      X ∉ Γ.freeTyVars →
      HasType (X :: Δ) Γ t A →
      HasType Δ Γ (.tyLam X t) (.all X A)
  | tyApp {Δ Γ f X A B C} :
      HasType Δ Γ f (.all X A) →
      Ty.subst? X B A = .ok C →
      HasType Δ Γ (.tyApp f B) C

def HasType.var' {Δ Γ x A} (h : Γ.lookup? x = some A) : HasType Δ Γ (.var x) A :=
  .var h

def HasType.lam' {Δ Γ x A t B} (cert : HasType Δ ((x, A) :: Γ) t B) :
    HasType Δ Γ (.lam x A t) (.arr A B) :=
  .lam cert

def HasType.lam_eq {Δ Γ x A B t C} (h : A = B) (cert : HasType Δ ((x, B) :: Γ) t C) :
    HasType Δ Γ (.lam x A t) (.arr B C) := by
  cases h
  exact .lam cert

def HasType.tyLam_eq {Δ Γ X Y t A} (h : X = Y) (hfresh : X ∉ Γ.freeTyVars)
    (cert : HasType (X :: Δ) Γ t A) :
    HasType Δ Γ (.tyLam X t) (.all Y A) := by
  cases h
  exact .tyLam hfresh cert

def HasType.app' {Δ Γ f a A B} (fn : HasType Δ Γ f (.arr A B))
    (arg : HasType Δ Γ a A) : HasType Δ Γ (.app f a) B :=
  .app fn arg

def HasType.tyApp' {Δ Γ f X A B C} (fn : HasType Δ Γ f (.all X A))
    (h : Ty.subst? X B A = .ok C) : HasType Δ Γ (.tyApp f B) C :=
  .tyApp fn h

end Logic.SystemF
