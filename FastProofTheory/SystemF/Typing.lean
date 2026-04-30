import FastProofTheory.SystemF.Syntax

namespace FastProofTheory.SystemF

abbrev DefaultLabel : Type := FastProofTheory.SystemF.Label

abbrev TyContext (α : Type := DefaultLabel) := List α

def TyContext.freeTyVars [DecidableEq α] (Δ : TyContext α) : List α :=
  Δ.eraseDups

inductive HasType (α : Type := DefaultLabel) [DecidableEq α] [ToString α] : TyContext α → Context α → Tm α → Ty α → Type where
  | var {Δ Γ x A} :
      Γ.lookup? x = some A →
      HasType α Δ Γ (.var x) A
  | lam {Δ Γ x A t B} :
      HasType α Δ ((x, A) :: Γ) t B →
      HasType α Δ Γ (.lam x A t) (.arr A B)
  | app {Δ Γ f a A B} :
      HasType α Δ Γ f (.arr A B) →
      HasType α Δ Γ a A →
      HasType α Δ Γ (.app f a) B
  | tyLam {Δ Γ X t A} :
      X ∉ Γ.freeTyVars →
      HasType α (X :: Δ) Γ t A →
      HasType α Δ Γ (.tyLam X t) (.all X A)
  | tyApp {Δ Γ f X A B C} :
      HasType α Δ Γ f (.all X A) →
      Ty.subst? X B A = .ok C →
      HasType α Δ Γ (.tyApp f B) C

def HasType.var' {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {x : α} {A : Ty α}
    (h : Γ.lookup? x = some A) : HasType α Δ Γ (.var x) A :=
  .var h

def HasType.lam' {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {x : α} {A B : Ty α} {t : Tm α}
    (cert : HasType α Δ ((x, A) :: Γ) t B) :
    HasType α Δ Γ (.lam x A t) (.arr A B) :=
  .lam cert

def HasType.lam_eq {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {x : α} {A B C : Ty α} {t : Tm α}
    (h : A = B) (cert : HasType α Δ ((x, B) :: Γ) t C) :
    HasType α Δ Γ (.lam x A t) (.arr B C) := by
  cases h
  exact .lam cert

def HasType.tyLam_eq {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {X Y : α} {t : Tm α} {A : Ty α}
    (h : X = Y) (hfresh : X ∉ Γ.freeTyVars)
    (cert : HasType α (X :: Δ) Γ t A) :
    HasType α Δ Γ (.tyLam X t) (.all Y A) := by
  cases h
  exact .tyLam hfresh cert

def HasType.app' {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {f a : Tm α} {A B : Ty α}
    (fn : HasType α Δ Γ f (.arr A B))
    (arg : HasType α Δ Γ a A) : HasType α Δ Γ (.app f a) B :=
  .app fn arg

def HasType.tyApp' {α : Type} [DecidableEq α] [ToString α]
    {Δ : TyContext α} {Γ : Context α} {f : Tm α} {X : α} {A B C : Ty α}
    (fn : HasType α Δ Γ f (.all X A))
    (h : Ty.subst? X B A = .ok C) : HasType α Δ Γ (.tyApp f B) C :=
  .tyApp fn h

end FastProofTheory.SystemF
