import sys
from collections import deque
from proveit import (Literal, Function, 
                     StyleOptions, USE_DEFAULTS, defaults,
                     equality_prover)
from proveit import A, B, C, D, E, F, G, h, i, j, k, m, n, p, Q, R, S, U
from proveit._core_.expression.composite import ExprArray, ExprTuple, ExprRange
from proveit.logic import Set
# from proveit.physics.quantum import Xgate, Ygate, Zgate, Hgate
# not clear yet what to substitute for ExpressionTensor -- perhaps ExprArray
# and Block is not being used in the active code
# from proveit.multi_expression import ExpressionTensor, Block
# from proveit.logic import Forall, Equals, InSet
# from proveit.computer_science.regular_expressions import KleeneRepetition

pkg = __package__  # can probably delete later

# quantum circuit gate literals

"""
# A BARRIER is required to separate independent gates that operate in parallel
# and are adjacent in a quantum circuit (e.g., no controlled gate between them):
BARRIER = literals.add('BARRIER', {STRING:'|', LATEX:'|'})
"""

"""
class ImplicitIdentities(Block):
    '''
    ImplicitIdentities are used in quantum circuits where they must be
    filled in with one or more identities as determined by the width of
    the circuit (which isn't established until Blocks are instantiated).
    See ForallWithImplicitIdentities.
    '''
    def __init__(self, name, format_map = None):
        Block.__init__(self, name, format_map)
"""

"""
def are_identities(gates):
    '''
    Returns the expression that the set of gates, as a List, are in the set of repeating identities.
    In other words, an expression that is true if all of the gates are identity gates.
    '''
    return In(List(gates), KleeneRepetition(I))



def _defineAxioms():
    return None # For now, we're just asserting the theorems without proof.

def _defineTheorems():
    _firstTheorem = \
    identity_collapse = ForallWithImplicitIdentities([Aetc, multi_b, Is], Equals(Circuit(Aetc, Gates(Is), multi_b), Circuit(Aetc, multi_b)))
    reverse_cz_dn = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is], Equals(Circuit(Aetc, Gates(multi_b, Target(Z), Is, CTRL_UP, Cetc), multi_d),
                                                                                            Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(Z), Cetc), multi_d)))
    reverse_cz_up = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is], Equals(Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(Z), Cetc), multi_d),
                                                                                            Circuit(Aetc, Gates(multi_b, Target(Z), Is, CTRL_UP, Cetc), multi_d)))
    reverse_cnot_dn_to_up = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is, IsB, IsC],
                                                     Equals(Circuit(Aetc, Gates(multi_b, CTRL_DN, Is, Target(X), Cetc), multi_d),
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multi_b, Target(X), Is, CTRL_UP, Cetc), Gates(IsB, H, Is, H, IsC), multi_d)))
    reverse_cnot_up_to_dn = ForallWithImplicitIdentities([Aetc, multi_b, Cetc, multi_d, Is, IsB, IsC],
                                                     Equals(Circuit(Aetc, Gates(multi_b, Target(X), Is, CTRL_UP, Cetc), multi_d),
                                                            Circuit(Aetc, Gates(IsB, H, Is, H, IsC), Gates(multi_b, CTRL_DN, Is, Target(X), Cetc), Gates(IsB, H, Is, H, IsC), multi_d)))
    return _firstTheorem, locals()
"""

class QcircuitElement(Function):
    def __init__(self,  operator, operand_or_operands, *, styles=None):
        Function.__init__(self, operator, operand_or_operands, styles=styles)

    def latex(self, *, within_qcircuit=False, **kwargs):
        '''
        Format the latex of the QcircuitElement.
        If within_qcircuit is false, we must wrap the LaTeX within
        a \Qcircuit command.
        If a 'wrapper' function is given, use it to
        generate dressed-up latex for the operand.
        '''
        out_str = self.circuit_elem_latex(solo=not within_qcircuit)
        if not within_qcircuit:
            # Do display it properly on its own, we need to
            # wrap it in a \Qcircuit latex command.
            spacing = '@C=1em @R=.7em'
            out_str = (r'\hspace{2em} \Qcircuit' + spacing + 
                       '{' + '\n' + '& ' + out_str + r' & \qw')
            out_str += ' \n' + r'} \hspace{2em}'
        return out_str
    
    def circuit_elem_latex(self, *, solo):
        '''
        LaTeX of the circuit element that may be inserted within a
        \Qcircuit LaTeX command given the LaTeX of the operand.
        If 'solo' is True, it is represented on its own and not within
        a broader circuit.
        '''
        raise NotImplementedError("Must implement for each QcircuitElement")
    
    def _config_latex_tool(self, lt):
        Function._config_latex_tool(self, lt)
        if 'qcircuit' not in lt.packages:
            lt.packages.append('qcircuit')


class Input(QcircuitElement):
    '''
    Represents an input state entering from the left-hand side of a
    circuit.
    '''
    # the literal operator of the Input operation class
    _operator_ = Literal('INPUT', theory=__file__)

    def __init__(self, state, *, styles=None):
        '''
        Create an INPUT operation (for entering the left-hand side
        of a circuit) with the given input state.
        '''
        QcircuitElement.__init__(self, Input._operator_, state, styles=styles)
        self.state = state

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Input circuit element.
        '''
        return r'\lstick{' + self.state.latex() + r'}'


class Output(QcircuitElement):
    '''
    Represents an output state exiting from the right-hand side of
    a circuit.
    '''
    # the literal operator of the Output operation class
    _operator_ = Literal('OUTPUT', theory=__file__)

    def __init__(self, state, *, styles=None):
        '''
        Create an OUTPUT operation with the given input state.
        '''
        QcircuitElement.__init__(self, Output._operator_, state, styles=styles)
        self.state = state

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Output circuit element.
        '''
        return r'\rstick{' + self.state.latex() + r'} \qw'


class Gate(QcircuitElement):
    '''
    Represents a gate in a quantum circuit.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GATE', theory=__file__)

    def __init__(self, operand, *, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        QcircuitElement.__init__(self, Gate._operator_, operand, styles=styles)
        self.gate_operation = self.operand
    
    def style_options(self):
        '''
        Return the StyleOptions object for this Gate object.
        '''
        from proveit.physics.quantum import I, X
        options = StyleOptions(self)
        if self.operand == I:
            # For an I gate, it may be displayed as
            # 'I' (explicit) or as a wire (implicit).
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the identity operation as "
                    "a quantum wire versus an 'explicit' gate (box) applying I."),
                default='implicit',
            related_methods=())
        if self.operand == X:
            # For an X gate, it may be displayed as
            # 'X' (explicit) or as a target (implicit).
            options.add_option(
                name='representation',
                description=(
                    "The 'implicit' option formats the X gate as "
                    "a target rather than 'X'."),
                default='explicit',
            related_methods=())

        return options
    
    def with_implicit_representation(self):
        return self.with_styles(representation='implicit')

    def with_explicit_representation(self):
        return self.with_styles(representation='explicit')
    
    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation', 'default')
        call_strs = []
        if representation == 'implicit':
            call_strs.append("with_implicit_representation()")
        elif representation == 'explicit':
            call_strs.append("with_explicit_representation()")
        return call_strs

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles "Gate(Input(U)) = Input(U)",
        and  "Gate(Output(U)) = Output(U)".
        '''
        if isinstance(self.gate_operation, Input):
            from proveit.physics.quantum import input_gate_to_ket
            return input_gate_to_ket.instantiate(
                {U: self.gate_operation.state})
        elif isinstance(self.gate_operation, Output):
            from proveit.physics.quantum import output_gate_to_ket
            return output_gate_to_ket.instantiate(
                {U: self.gate_operation.state})
        return QcircuitElement.shallow_simplification(
                self, must_evaluate=must_evaluate)

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Gate circuit element.
        '''
        from proveit.physics.quantum import I, X, MEAS
        if self.gate_operation == MEAS:
            return r'\meter'
        if self.operand == I:
            if self.get_style('representation') == 'implicit':
                return r'\qw'
        if (self.operand == X and
                self.get_style('representation') == 'implicit'):
            return r'\targ'
        elif isinstance(self.gate_operation, Input):
            return r'\gate{INPUT(' + self.gate_operation.state.latex() + r')}'
        elif isinstance(self.gate_operation, Output):
            return r'\gate{OUTPUT(' + self.gate_operation.state.latex() + r')}'
        else:
            return r'\gate{' + self.gate_operation.latex() + r'}'

class Ghost(QcircuitElement):
    '''
    Represents a portion of a multi-gate that isn't the top-most
    portion.  The top-most portion should be a MultiQuditGate.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('GHOST', theory=__file__)

    def __init__(self, operand, *, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        QcircuitElement.__init__(self, Ghost._operator_, operand, styles=styles)
        self.gate_operation = self.operand

    def operand_latex(self, wrapper=None):
        '''
        LaTeX of the operand, dressed-up using an optional 'wrapper'
        function.
        
        Handle Input, Output gate operations as special cases.
        '''
        if isinstance(self.gate_operation, Input):
            formatted_operand = 'Input(%s)'%self.gate_operation.state.latex(
                    fence=False)
        elif isinstance(self.gate_operation, Output):
            formatted_operand = 'Output(%s)'%self.gate_operation.state.latex(
                    fence=False)
        else:
            formatted_operand = self.gate_operation.latex(fence=False)
        if wrapper is not None:
            formatted_operand = wrapper(formatted_operand)

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this Gate circuit element.
        '''
        if solo:
            # Put ':' above and below to denote that this just
            # represents a portion of a multi-gate.
            return (r'\gate{\begin{array}{c} : \\ %s \\ : \end{array}}'
                    %self.gate_operation.latex())
        else:
            # A \ghost for a \multigate.
            return r'\ghost{%s}'%self.gate_operation.latex()

class MultiQuditGate(QcircuitElement):
    '''
    A MultiQuditGate is a quantum circuit element that expresses
    an operation involving multiple rows that each may represent
    one or more qubits (a qudit).
    
    The sub-expressions are the gate operation and the qudit_positions.
    The qudit_positions may be an ExprTuple, Set, or an expression
    representing either of these.
    
    A generic MultiQuditGate will use an expression to represent
    a ExprTuple or Set of qudit_positions that is not an ExprTuple
    or Set.  
    
    For controlled gate, there should be a MultiQuditGate at the
    control with a CONTROL gate_operation, and the qudit_positions
    should be a Set with the positions of the control and the targets.
    It should use a Set since order doesn't matter.  The targets can be
    normal Gate elements but may be multi-gates.
    
    A multi-gate (a tall box covering multiple rows) should use a
    MultiQuditGate at the top row of the multi-gate and Ghost elements
    for the other rows.  The qudit_positions should be an ExprTuple
    of the consecutive positions starting with the top 
    "representative".  The order doesn't matter; we must not allow
    the qudits involved in a mult-gate to be permuted.  A controlled 
    gate may have multi-gate target(s); the top "representative" should
    be used as the target.
    
    A Toffoli gate should be treated as multiple controlled gates with
    the same target.
    
    A swap gate should be redudant with two MultiQuditGates using
    SWAP as the gate operation of each.  Each one should list its own 
    position as the first of the qudit_positions and the other as the 
    second.  Although this is redundant, it ensures that there is one 
    way to represent this symmetric operation.
    
    A controlled-Z expressed in a symmetric manner (with a filled-in
    control dot on each end), should be implemented in the redundant
    manner of the swap gate, but with CONTROL as the gate_operation.
    '''
    # the literal operator of the Gate operation class
    _operator_ = Literal('MULTI_QUDIT_GATE', theory=__file__)

    def __init__(self, gate_operation, qudit_positions, *, styles=None):
        '''
        Create a quantum circuit gate performing the given operation.
        '''
        Function.__init__(self, MultiQuditGate._operator_,
                           (gate_operation, qudit_positions), styles=styles)
        self.gate_operation = self.operands[0]
        self.qudit_positions = self.operands[1]
        if isinstance(gate_operation, MultiQuditGate):
            raise TypeError("A MultiQuditGate should not have a "
                            "MultiQuditGate as it's 'gate'")

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        # It would be better to make this only an option when it is
        # applicable.  Just doing this for now.
        options.add_option(
            name='representation',
            description=("'implicit' representation displays X gates "
                         "as a target, while 'explicit' representation "
                         "always displays the type of gate in a box. "
                         "Ex. |X|. 'Block' displays the MultiQubitGate "
                         "as a block gate assuming all other gates within"
                         " the MultiQubitGate are the same."),
            default='implicit',
            related_methods=())

        # options.add_option(
        #     name='set_representation',
        #     description=("'implicit' representation does not display the set "
        #                  "but 'explicit representation does. "),
        #     default='default',
        #     related_methods=('with_explicit_set_representation',
        #                      'with_implicit_set_representation'))

        return options

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation')
        call_strs = []
        if representation != 'explicit':
            call_strs.append("with_styles(representation='%s')"
                             %representation)
        return call_strs

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this MultiQuditGate circuit element.
        If solo=True, the MultiQuditGate will be display on its own
        rather than in the context of a broader Qcircuit.
        '''
        from proveit.physics.quantum import (CONTROL, CLASSICAL_CONTROL, 
                                             X, SWAP)
        
        if not solo and (isinstance(self.qudit_positions, Set) or
                         isinstance(self.qudit_positions, ExprTuple)):
            # This will be shown in the context of a broader Qcircuit
            # and has explicit qudit positions.
            if self.gate_operation == CONTROL:
                return r'\control \qw'
            elif self.gate_operation == CLASSICAL_CONTROL:
                return r'\control \cw'
            if self.gate_operation == X:
                if self.get_style('representation') == 'implicit':
                    return r'\targ'
            elif self.gate_operation == SWAP:
                return r'\qswap'
            return r'\gate{' + self.gate_operation.latex() + r'}'
        else:
            # This is either being shown on its own, or it lacks
            # explicit qudit positions.
            return (r'\gate{%s : %s}'
                    %(self.gate_operation.latex(), 
                      self.qudit_positions.latex()))

    @equality_prover('shallow_simplified', 'shallow_simplify')
    def shallow_simplification(self, *, must_evaluate=False,
                               **defaults_config):
        '''
        Handles "MultiQubitGate(a, Set()) = IdentityOp()" and
        "MultiQubitGate(a, Set(n)) = Gate(a)".
        '''
        from proveit.numbers import is_literal_int
        from proveit.logic.equality import Equals
        if (isinstance(self.qudit_positions, ExprTuple) 
                and self.qudit_positions.is_single()
                and is_literal_int(self.gate_set.operands[0])):
            try:
                return self.unary_reduction()
            except BaseException:
                # Cannot do the reduction if the operand is not known
                # to be in NaturalPos.
                pass

        if (isinstance(self.qudit_positions, ExprTuple) and 
                self.qudit_positions.num_entries() == 0):
            return self.empty_set_reduction()
            # need to implement an empty set reduction theorem
        return Equals(self, self).conclude_via_reflexivity()

    @equality_prover('unary_reduced', 'unary_reduce')
    def unary_reduction(self, **defaults_config):
        from proveit.physics.quantum.circuits import (
                unary_multi_qudit_gate_reduction)
        if not isinstance(self.qudit_positions, ExprTuple):
            raise TypeError("'qudit_positions' must be an ExprTuple in "
                            "order to invoke unary_reduction")
        if not self.qudit_positions.is_single():
            raise ValueError("'qudit_positions' must be a singular "
                             "ExprTuple in order to invoke unary_reduction")
        operand = self.qudit_positions.operands[0]
        return unary_multi_qudit_gate_reduction.instantiate(
            {U: self.gate_operation, A: operand})

    @equality_prover('empty_set_reduced', 'empty_set_reduce')
    def empty_reduction(self, **defaults_config):
        from proveit.physics.quantum.circuits import (
                empty_multi_qudit_gate_reduction)
        if not isinstance(self.qudit_positions, ExprTuple):
            raise TypeError("'qudit_positions' must be an ExprTuple in "
                            "order to invoke empty_reduction")
        if self.qudit_positions.num_entries() != 0:
            raise ValueError("'qudit_positions' must be an empty "
                             "ExprTuple in order to invoke empty_reduction")
        return empty_multi_qudit_gate_reduction.instantiate(
            {U: self.gate_operation})


class MultiWire(QcircuitElement):
    '''
    Marks a "wire" as a bundle with a number of individual wires.
    '''
    _operator_ = Literal('MULTI_WIRE', theory=__file__)

    def __init__(self, number, *, styles=None):
        '''
        Create a multi-wire.
        '''
        Function.__init__(self, MultiWire._operator_, number,
                          styles=styles)
        self.number = number

    def remake_with_style_calls(self):
        '''
        In order to reconstruct this Expression to have the same styles,
        what "with..." method calls are most appropriate?
        '''
        representation = self.get_style('representation', 'explicit')
        call_strs = []
        if representation != 'explicit':
            call_strs.append("with_styles(representation='%s')"
                             %representation)
        return call_strs

    def style_options(self):
        from proveit._core_.expression.style_options import StyleOptions

        options = StyleOptions(self)
        # It would be better to make this only an option when it is
        # applicable.  Just doing this for now.
        options.add_option(
            name='representation',
            description=("'implicit' representation displays MutiWire"
                         "objects as an IdentityOp. 'explicit' representation "
                         "displays MultiWire objects as a bundle using the "
                         "backslash notation. "),
            default='explicit',
            related_methods=('with_implicit_style'))

        return options

    def with_implicit_style(self):
        '''
        return a MultiWire object with the implicit style
        '''
        return self.with_styles(representation='implicit')

    def circuit_elem_latex(self, *, solo):
        '''
        Display the LaTeX for this MultiWire circuit element.
        '''
        representation = self.get_style('representation', 'explicit')
        if representation == 'explicit':
            return r'{ /^{' + self.number.latex() + r'} } \qw'
        else:
            return r'\qw'