import Logic.SystemF.Syntax

namespace Logic.SystemF

inductive HasType : Context → Tm → Ty → Type where
  | var {Γ : Context} {x : String} {A : Ty} :
      Γ.lookup? x = some A →
      HasType Γ (.var x) A
  | arrIntro {Γ : Context} {x : String} {A B : Ty} {body : Tm} :
      HasType ((x, A) :: Γ) body B →
      HasType Γ (.lam x A body) (.arr A B)
  | arrElim {Γ : Context} {fn arg : Tm} {A B : Ty} :
      HasType Γ fn (.arr A B) →
      HasType Γ arg A →
      HasType Γ (.app fn arg) B
  | allIntro {Γ : Context} {p : String} {body : Tm} {A : Ty} :
      p ∉ Γ.freeTyVars →
      HasType Γ body A →
      HasType Γ (.tyLam p body) (.all p A)
  | allElim {Γ : Context} {fn : Tm} {p : String} {A B instantiated : Ty} :
      Ty.subst? p B A = .ok instantiated →
      HasType Γ fn (.all p A) →
      HasType Γ (.tyApp fn B) instantiated

end Logic.SystemF
