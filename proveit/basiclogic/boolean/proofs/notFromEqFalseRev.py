from proveit.basiclogic import Implies, Equals, FALSE
from proveit.basiclogic.variables import A

# FeqA := (F=A)
FeqA = Equals(FALSE, A)
# Not(A) assuming FeqA
notA = FeqA.deriveReversed().deriveViaBooleanEquality().prove({FeqA})
Implies(FeqA, notA).generalize(A).qed(__file__)
