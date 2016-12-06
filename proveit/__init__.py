from _core_ import defaults, USE_DEFAULTS, InvalidAssumptions, storage
from _core_ import Expression, Operation, Lambda, Label, Variable, MultiVariable, Literal, Etcetera, Block, safeDummyVar, tryDerivation
from _core_ import MakeNotImplemented, ImproperRelabeling, ImproperSubstitution, ScopingViolation, ProofFailure
from _core_ import ExpressionList, ExpressionTensor, NamedExpressions, Composite, compositeExpression, singleOrCompositeExpression, NestedCompositeExpressionError
from _core_ import beginAxioms, endAxioms, beginTheorems, endTheorems, KnownTruth, asExpression, asExpressions
from _core_ import Proof, Assumption, Axiom, Theorem, ModusPonens, HypotheticalReasoning, Specialization, Generalization
from _core_ import ModusPonensFailure, RelabelingFailure, SpecializationFailure, GeneralizationFailure
from _generic_ import BinaryOperation, AssociativeOperation, OperationOverInstances, InstanceSubstitutionException
from _generic_ import maybeFencedString, maybeFencedLatex, maybeFenced

# Implies, Forall, and InSet are core concepts that are defined outside of the core.
from proveit.logic import Implies, Forall, InSet

# These methods are called within the core as convenience methods (not really core concepts)
from proveit.logic import reduceOperands, proveViaReduction, defaultEvaluate, evaluateTruth

