import FastProofTheory.Rules
import FastProofTheory.LK2
import FastProofTheory.SystemF.Syntax
import FastProofTheory.SystemF.Typing

namespace FastProofTheory.Language

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
    , parserEntryPoint := "FastProofTheory.LK2"
    , renderEntryPoint := "FastProofTheory.LK2.SingleSorted" },
    { kind := .systemFTypedTerm
    , displayName := "System F typed terms"
    , supportedDeclarationNames := ["SYSTEM_F"]
    , parserEntryPoint := "FastProofTheory.SystemF.Syntax.parseJudgment"
    , renderEntryPoint := "FastProofTheory.SystemF.Typing.HasType" } ]

def syntaxDescriptor? (obj : ObjectSyntax) : Option SyntaxDescriptor :=
  syntaxRegistry.find? (fun d => d.kind = obj)

end FastProofTheory.Language
