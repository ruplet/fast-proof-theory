import Logic.Rules
import Logic.LK2
import Logic.SystemF.Syntax
import Logic.SystemF.Typing

namespace Logic

inductive ObjectSyntax where
  | propositional
  | firstOrder
  | lk2
  | systemFTypedTerm
deriving DecidableEq, Repr

structure SyntaxDescriptor where
  kind : ObjectSyntax
  displayName : String
  supportedDeclarationNames : List String
  parserEntryPoint : String
  renderEntryPoint : String
deriving Repr

def syntaxRegistry : List SyntaxDescriptor :=
  [ { kind := .propositional
    , displayName := "Propositional logic"
    , supportedDeclarationNames := ["NJp", "NKp", "LJp", "LKp", "LL", "LL!"]
    , parserEntryPoint := "FastProofTheory.Linear.Syntax.parseSurfaceFormula"
    , renderEntryPoint := "FastProofTheory.Linear.Syntax.renderFormula" },
    { kind := .firstOrder
    , displayName := "First-order logic"
    , supportedDeclarationNames := ["NJ", "NK", "LJ", "LK"]
    , parserEntryPoint := "FastProofTheory.Linear.Syntax.parseFormula"
    , renderEntryPoint := "FastProofTheory.Linear.Syntax.renderFormula" },
    { kind := .lk2
    , displayName := "LK2 two-sorted logic"
    , supportedDeclarationNames := ["LK2"]
    , parserEntryPoint := "Logic.LK2"
    , renderEntryPoint := "Logic.LK2.SingleSorted" },
    { kind := .systemFTypedTerm
    , displayName := "System F typed terms"
    , supportedDeclarationNames := ["SYSTEM_F"]
    , parserEntryPoint := "FastProofTheory.SystemF.Syntax.parseJudgment"
    , renderEntryPoint := "Logic.SystemF.Typing.HasType" } ]

def syntaxDescriptor? (obj : ObjectSyntax) : Option SyntaxDescriptor :=
  syntaxRegistry.find? (fun d => d.kind = obj)

end Logic
