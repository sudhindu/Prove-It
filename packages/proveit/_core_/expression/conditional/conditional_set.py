from proveit._core_.expression.label.literal import Literal
from proveit._core_.expression.operation import Operation
from proveit._core_.defaults import defaults, USE_DEFAULTS


class ConditionalSet(Operation):
    # operator of the ConditionalSet operation
    _operator_ = Literal(string_format='CondSet',
                         latex_format=r'\textrm{CondSet}', theory=__file__)

    def __init__(self, *conditionals):
        Operation.__init__(self, ConditionalSet._operator_, conditionals)
        self.conditionals = self.operands

    def auto_reduction(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce a conditional set with one and only one TRUE condition
        where the other conditions are FALSE.
        '''
        self.reduce_to_truth(assumptions=assumptions)

    def reduce_to_truth(self, assumptions=USE_DEFAULTS):
        '''
        Automatically reduce a conditional set with one and only one TRUE condition
        where the other conditions are FALSE.
        '''
        from proveit import a, b, c, m, n
        from proveit.logic import FALSE, TRUE
        from proveit.core_expr_types.conditionals import singular_truth_reduction

        _b = None
        index = None
        for i, item in enumerate(self.conditionals):
            if item.condition == TRUE:
                if _b is not None:
                    return
                _b = item.value
                index = i
            else:
                assert item.condition == FALSE
        _a = [con.value for con in self.conditionals[:index]]
        _c = [con.value for con in self.conditionals[index+1:]]
        _m = self.conditionals[:index].num_elements(assumptions)
        _n = self.conditionals[index+1:].num_elements(assumptions)
        return singular_truth_reduction.instantiate({m: _m, n: _n, a: _a, b: _b, c: _c}, assumptions=assumptions)

    def string(self, **kwargs):
        inner_str = '; '.join(conditional.string(fence=False)
                              for conditional in self.conditionals)
        return '{' + inner_str + '.'

    def latex(self, **kwargs):
        inner_str = r' \\ '.join(conditional.latex(fence=False)
                                 for conditional in self.conditionals)
        inner_str = r'\begin{array}{ccc}' + inner_str + r'\end{array}'
        inner_str = r'\left\{' + inner_str + r'\right..'
        return inner_str
