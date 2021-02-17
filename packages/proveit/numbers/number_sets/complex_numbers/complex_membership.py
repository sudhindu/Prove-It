from proveit import USE_DEFAULTS
from proveit import x
from proveit.logic import NotEquals, InSet
from proveit.numbers import (zero, Complex, ComplexNonZero)
from proveit.numbers.number_sets.number_set import NumberMembership


class ComplexNonZeroMembership(NumberMembership):

    '''
    Defines methods that apply to membership in RationalNonZero
    '''

    def __init__(self, element):
        NumberMembership.__init__(self, element, ComplexNonZero)

    def conclude(self, assumptions=USE_DEFAULTS):
        if (InSet(self.element, Complex).proven(assumptions) and
                NotEquals(self.element, zero).proven(assumptions)):
            from . import nonzero_complex_is_complex_nonzero
            return nonzero_complex_is_complex_nonzero.instantiate(
                    {x:self.element}, assumptions=assumptions)
        return NumberMembership.conclude(self, assumptions)
