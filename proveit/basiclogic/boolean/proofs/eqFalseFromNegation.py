from proveit.basiclogic import Implies, Not
from proveit.basiclogic.variables import A

# Not(Not(A)) assuming A
notNotA = Not(Not(A)).concludeViaDoubleNegation()
Implies(A, notNotA.equateNegatedToFalse()).generalize(A).qed(__file__)
