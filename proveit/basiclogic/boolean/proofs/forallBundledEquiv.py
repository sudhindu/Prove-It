from proveit.basiclogic.boolean.theorems import forallBundling, forallUnraveling
from proveit.basiclogic import Iff
from proveit.basiclogic.variables import P, S
from proveit.basiclogic.simpleExpr import etcQ, etcR

# forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..) => forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..)
forallBundlingSpec = forallBundling.specialize().prove()
# forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) => forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
forallUnraveling.specialize().prove()
# lhs = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)
# rhs = forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) 
lhs, rhs = forallBundlingSpec.conclusion, forallBundlingSpec.hypothesis
# lhs in BOOLEANS, rhs in BOOLEANS
for expr in (lhs, rhs): expr.deduceInBool().prove()
# lhs = rhs
equiv = Iff(lhs, rhs).concludeViaComposition().deriveEquality().prove()
# forall_{P, ..Q.., ..R.., S} [forall_{..x.., ..y.. in S | ..Q(..x..).., ..R(..y..)..} P(..x.., ..y..) = forall_{..x.. in S | ..Q(..x..)..} forall_{..y.. in S | ..R(..y..)..} P(..x.., ..y..)]
equiv.generalize((P, etcQ, etcR, S)).qed(__file__)
