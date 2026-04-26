import FastProofTheory.Server.Protocol

namespace FastProofTheory.Server.Domain

open Lean
open FastProofTheory.Server

/--
Lean-owned presentation metadata for the MyPA language.

This module is intentionally outside the TypeScript client/LSP.  The editor may
render this information, but the proof-system names, tactic names, rule displays,
and supported formula syntax are owned by the Lean backend next to the checkers.
The trusted proof-checking code remains in:

* `FastProofTheory.ND.Kernel`
* `FastProofTheory.Gentzen.Kernel`

System F scripts are elaborated into natural-deduction certificates and checked
by `FastProofTheory.ND.Kernel`; there is no separate trusted System F kernel.
The execution/certificate builders in `FastProofTheory.Linear.Engine` elaborate
user tactics into certificates checked by the kernels above.
-/

structure SymbolCompletion where
  label : String
  insertText : String
  detail : String := ""
  documentation : String := ""
deriving Inhabited, Repr, ToJson, FromJson

structure DirectiveCompletion where
  label : String
  insertText : String
  detail : String := ""
  documentation : String := ""
deriving Inhabited, Repr, ToJson, FromJson

structure TacticDoc where
  name : String
  title : String
  display : String
  summary : String := ""
deriving Inhabited, Repr, ToJson, FromJson

structure FormalSystemDoc where
  key : String
  aliases : List String := []
  title : String
  summary : String
  language : List String
  tactics : List TacticDoc
  checkedNow : List String
deriving Inhabited, Repr, ToJson, FromJson

structure DomainInfo where
  symbolCompletions : List SymbolCompletion
  directives : List DirectiveCompletion
  systems : List FormalSystemDoc
  keywords : List String
  operators : List String
deriving Inhabited, Repr, ToJson, FromJson

def symbolCompletions : List SymbolCompletion := [
  { label := "\\otimes", insertText := "⊗", detail := "tensor / times" },
  { label := "\\tensor", insertText := "⊗", detail := "tensor / times" },
  { label := "\\lolli", insertText := "⊸", detail := "linear implication" },
  { label := "\\with", insertText := "&", detail := "with" },
  { label := "\\plus", insertText := "⊕", detail := "plus" },
  { label := "\\oplus", insertText := "⊕", detail := "plus" },
  { label := "\\and", insertText := "∧", detail := "conjunction" },
  { label := "\\or", insertText := "∨", detail := "disjunction" },
  { label := "\\imp", insertText := "⟶", detail := "intuitionistic implication" },
  { label := "\\to", insertText := "⟶", detail := "intuitionistic implication" },
  { label := "\\top", insertText := "⊤", detail := "top" },
  { label := "\\bot", insertText := "⊥", detail := "bottom" },
  { label := "\\bottom", insertText := "⊥", detail := "bottom" },
  { label := "\\one", insertText := "1", detail := "linear unit" },
  { label := "\\zero", insertText := "0", detail := "linear zero" },
  { label := "\\bang", insertText := "!", detail := "of course" }
]

def directives : List DirectiveCompletion := [
  {
    label := "#help",
    insertText := "#help ",
    detail := "Show formal-system help",
    documentation := "Display the language and inference rules for a supported formal system."
  }
]

def linearTactics : List TacticDoc := [
  { name := "ax", title := "Axiom", display := "A ⊢ A", summary := "Identity / axiom." },
  { name := "rlolli", title := "Right Lolli", display := "Γ, A ⊢ B, Δ\n────────────── rlolli\nΓ ⊢ A ⊸ B, Δ", summary := "Right introduction for linear implication." },
  { name := "rtensor", title := "Right Tensor", display := "Γ ⊢ A, Δ    Π ⊢ B, Σ\n──────────────────── rtensor\nΓ, Π ⊢ A ⊗ B, Δ, Σ", summary := "Right introduction for tensor with a resource split." },
  { name := "rwith", title := "Right With", display := "Γ ⊢ A, Δ    Γ ⊢ B, Δ\n──────────────────── rwith\nΓ ⊢ A & B, Δ", summary := "Right introduction for additive conjunction." },
  { name := "lleft", title := "Left With-1", display := "Γ, A ⊢ Δ\n────────── lleft at h\nΓ, A & B ⊢ Δ", summary := "Use the left component of a with-hypothesis." },
  { name := "lright", title := "Left With-2", display := "Γ, B ⊢ Δ\n────────── lright at h\nΓ, A & B ⊢ Δ", summary := "Use the right component of a with-hypothesis." },
  { name := "ltensor", title := "Left Tensor", display := "Γ, A, B ⊢ Δ\n──────────── ltensor at h\nΓ, A ⊗ B ⊢ Δ", summary := "Decompose a tensor hypothesis." },
  { name := "lplus", title := "Left Plus", display := "Γ, A ⊢ Δ    Γ, B ⊢ Δ\n──────────────────── lplus at h\nΓ, A ⊕ B ⊢ Δ", summary := "Eliminate an additive disjunction hypothesis." },
  { name := "rplusl", title := "Right Plus-1", display := "Γ ⊢ A, Δ\n────────── rplusl\nΓ ⊢ A ⊕ B, Δ", summary := "Left injection for plus." },
  { name := "rplusr", title := "Right Plus-2", display := "Γ ⊢ B, Δ\n────────── rplusr\nΓ ⊢ A ⊕ B, Δ", summary := "Right injection for plus." },
  { name := "llolli", title := "Left Lolli", display := "Γ ⊢ A, Δ    Π, B ⊢ Σ\n──────────────────── llolli at h\nΓ, Π, A ⊸ B ⊢ Δ, Σ", summary := "Eliminate a linear implication hypothesis." },
  { name := "lbang", title := "Left Bang", display := "Γ, A ⊢ Δ\n──────── lbang at h\nΓ, !A ⊢ Δ", summary := "Move a banged linear hypothesis into unrestricted use." },
  { name := "rbang", title := "Right Bang", display := "!Γ ⊢ A\n────── rbang\n!Γ ⊢ !A", summary := "Introduce bang when the linear context is unrestricted." }
]

def ndTactics : List TacticDoc := [
  { name := "intro", title := "Implication Introduction", display := "A, Γ ⊢ B\n────────── intro h\nΓ ⊢ A ⟶ B", summary := "Introduce an implication by assuming its premise." },
  { name := "assumption", title := "Assumption", display := "A ∈ Γ\n────── assumption h\nΓ ⊢ A", summary := "Close a goal from a matching hypothesis." },
  { name := "constructor", title := "Conjunction Introduction", display := "Γ ⊢ A    Γ ⊢ B\n──────────────── constructor\nΓ ⊢ A ∧ B", summary := "Split a conjunction goal." },
  { name := "left", title := "Left Rule", display := "Goal: Γ ⊢ A ∨ B  gives Γ ⊢ A\nHyp: h : A ∧ B gives h : A", summary := "Left disjunction introduction or first conjunction projection." },
  { name := "right", title := "Right Rule", display := "Goal: Γ ⊢ A ∨ B  gives Γ ⊢ B\nHyp: h : A ∧ B gives h : B", summary := "Right disjunction introduction or second conjunction projection." },
  { name := "cases", title := "Disjunction Elimination", display := "Γ ⊢ A ∨ B    A, Γ ⊢ C    B, Γ ⊢ C\n──────────────────────────── cases at h as hp hq\nΓ ⊢ C", summary := "Eliminate a disjunction hypothesis." },
  { name := "apply", title := "Implication Elimination", display := "h : A ⟶ B    Goal: B\n──────────── apply h\nNew goal: A", summary := "Use an implication hypothesis to reduce the goal to its premise." },
  { name := "exfalso", title := "Bottom Goal", display := "Goal: C\n──────── exfalso\nGoal: ⊥", summary := "Replace the current target by bottom." },
  { name := "absurd", title := "Bottom Elimination", display := "h : ⊥\n────── absurd h\nΓ ⊢ C", summary := "Close any goal from a contradiction." }
]

def cpcOnlyTactics : List TacticDoc := [
  { name := "by_contra", title := "Classical Rule", display := "(A ⟶ ⊥), Γ ⊢ ⊥\n──────────────── by_contra h\nΓ ⊢ A", summary := "Classical reasoning by contradiction." }
]

def systems : List FormalSystemDoc := [
  {
    key := "cllp_gentzen",
    aliases := ["ll_gentzen"],
    title := "Classical Linear Logic, Gentzen Sequent Calculus",
    summary := "Classical linear propositional calculus in Urzyczyn-style sequent calculus.",
    language := [
      "Formulas: A, B ::= p | A ⊗ B | A & B | A ⊕ B | A ⅋ B | A ⊸ B | !A | 1 | 0 | ⊤ | ⊥",
      "Sequents are displayed as Left ⊢ Right."
    ],
    tactics := linearTactics,
    checkedNow := ["ax", "rlolli", "rtensor", "rwith", "rplusl", "rplusr", "lleft", "lright", "ltensor", "lplus", "llolli", "lbang", "rbang"]
  },
  {
    key := "njp_nd",
    title := "NJp - Intuitionistic Propositional Natural Deduction",
    summary := "Intuitionistic propositional natural deduction.",
    language := [
      "Formulas: A, B ::= p | A ∧ B | A ∨ B | A ⟶ B | ⊥",
      "Proof state is displayed as hypotheses together with a single current target."
    ],
    tactics := ndTactics,
    checkedNow := ndTactics.map (·.name)
  },
  {
    key := "nkp_nd",
    title := "NKp - Classical Propositional Natural Deduction",
    summary := "Classical propositional natural deduction.",
    language := [
      "Formulas: A, B ::= p | A ∧ B | A ∨ B | A ⟶ B | ⊥",
      "This extends NJp in ND with one classical tactic."
    ],
    tactics := ndTactics ++ cpcOnlyTactics,
    checkedNow := (ndTactics ++ cpcOnlyTactics).map (·.name)
  },
  {
    key := "ljp",
    title := "LJp - Intuitionistic Propositional Sequent Calculus",
    summary := "Recognized by the parser, but the sequent-script checker is not wired up yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  },
  {
    key := "lkp",
    title := "LKp - Classical Propositional Sequent Calculus",
    summary := "Recognized by the parser, but the sequent-script checker is not wired up yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  },
  {
    key := "nj",
    title := "NJ - Intuitionistic First-Order Natural Deduction",
    summary := "Recognized by the parser, but first-order quantifier checking is not available yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  },
  {
    key := "nk",
    title := "NK - Classical First-Order Natural Deduction",
    summary := "Recognized by the parser, but first-order quantifier checking is not available yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  },
  {
    key := "lj",
    title := "LJ - Intuitionistic First-Order Sequent Calculus",
    summary := "Recognized by the parser, but first-order quantifier checking is not available yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  },
  {
    key := "lk",
    title := "LK - Classical First-Order Sequent Calculus",
    summary := "Recognized by the parser, but first-order quantifier checking is not available yet.",
    language := [
      "This system is currently unavailable in the checker."
    ],
    tactics := [],
    checkedNow := []
  }
]

def allTactics : List TacticDoc :=
  (systems.foldl (fun acc system => acc ++ system.tactics) []).foldl
    (fun acc tactic =>
      if acc.any (fun existing => existing.name = tactic.name) then acc else tactic :: acc)
    []
    |>.reverse

def keywords : List String :=
  [
    "theorem", "def", "using", "tactic", "at", "as", "with",
    "type_intro", "type_apply", "exact", "translate", "translate_to", "solve_np"
  ] ++ allTactics.map (·.name)

def operators : List String := ["⊗", "⊕", "∧", "∨", "⊸", "⟶", "&", "!", ":"]

def domainInfo : DomainInfo := {
  symbolCompletions := symbolCompletions
  directives := directives
  systems := systems
  keywords := keywords
  operators := operators
}

def findSystem? (name : String) : Option FormalSystemDoc :=
  let normalized := name.toLower
  systems.find? (fun system =>
    system.key.toLower = normalized || system.aliases.any (fun alias => alias.toLower = normalized))

def knownSystemNames : List String :=
  systems.foldl (fun acc system => acc ++ (system.key :: system.aliases)) []

def systemHelpDisplay (name : String) : ProofDisplay :=
  match findSystem? name with
  | some system =>
      {
        title := s!"Help: {name}",
        status := system.summary,
        sections := [
          { title := "System", body := [system.title] },
          { title := "Language", body := system.language },
          { title := "Tactics And Rules", body := system.tactics.map (fun tactic => s!"{tactic.name}: {tactic.summary}") },
          { title := "Checked Now", body := system.checkedNow }
        ]
      }
  | none =>
      {
        title := s!"Help: {name}",
        status := s!"Unknown formal system `{name}`.",
        sections := [
          { title := "Known Systems", body := knownSystemNames }
        ]
      }

end FastProofTheory.Server.Domain
