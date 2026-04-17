namespace Substructural

inductive StructuralMode where
| ordered
| linear
| affine
| relevant
| normal
deriving DecidableEq, Repr

def allowsExchange : StructuralMode -> Bool
| .ordered => false
| .linear => true
| .affine => true
| .relevant => true
| .normal => true

def allowsWeakening : StructuralMode -> Bool
| .ordered => false
| .linear => false
| .affine => true
| .relevant => false
| .normal => true

def allowsContraction : StructuralMode -> Bool
| .ordered => false
| .linear => false
| .affine => false
| .relevant => true
| .normal => true

def usageSummary : StructuralMode -> String
| .ordered => "exactly once, in order"
| .linear => "exactly once"
| .affine => "at most once"
| .relevant => "at least once"
| .normal => "arbitrarily"

def intuitionisticMode : StructuralMode := .normal
def linearMode : StructuralMode := .linear

end Substructural
