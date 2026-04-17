universe u v

-- for any type family β, [] is a valid list over that family
-- then, we can create a list over β with indexes (x :: xs) if for some
-- index x and for a list of indexes xs, we can obtain an element of type β x
-- and a HList of elements that should lay on positions from `xs`.
inductive HList {α : Type u} (β : α → Type v) : List α → Type (max u v) where
  | nil : HList β []
  | cons : β x → HList β xs → HList β (x :: xs)

structure InferenceSystem where
  Judgment   : Type u
  RuleName   : Type v
  Rule       : Type (max u v)
  ruleName   : Rule → RuleName
  premises   : Rule → List Judgment
  conclusion : Rule → Judgment

inductive Proof (S : InferenceSystem.{u', v'}) : S.Judgment → Type (max u' v') where
  | byRule
      (r : S.Rule)
      (subproofs : HList (fun j => Proof S j) (S.premises r)) :
      Proof S (S.conclusion r)
